package com.intellij.codeInspection;

import com.intellij.openapi.diagnostic.Logger;
import com.intellij.openapi.editor.Document;
import com.intellij.openapi.fileEditor.FileDocumentManager;
import com.intellij.openapi.module.Module;
import com.intellij.openapi.module.ModuleUtil;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.roots.ProjectFileIndex;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.psi.*;
import com.intellij.psi.impl.java.stubs.JavaLiteralExpressionElementType;
import com.intellij.psi.impl.source.tree.java.PsiReferenceExpressionImpl;
import com.intellij.psi.search.ProjectScope;
import com.intellij.psi.search.searches.MethodReferencesSearch;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.util.IncorrectOperationException;
import org.apache.commons.lang3.StringUtils;
import org.assertj.core.util.Sets;
import org.jetbrains.annotations.Nls;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author max
 * @author jhake
 */
public class NonExistingSqlParamInspection extends AbstractBaseJavaLocalInspectionTool {
    private static final Logger LOG = Logger.getInstance("#com.intellij.codeInspection.NonExistingSqlParamInspection");
    public static final String PLACE_HOLDER_SEPARATOR_REGEX = "[ ,)(\n;\r\t|=><]";


    /**
     * This method is overridden to provide a custom visitor
     * that inspects expressions with relational operators '==' and '!='
     * The visitor must not be recursive and must be thread-safe.
     *
     * @param holder     object for visitor to register problems found.
     * @param isOnTheFly true if inspection was run in non-batch mode
     * @return non-null visitor for this inspection.
     * @see JavaElementVisitor
     */
    @NotNull
    @Override
    public PsiElementVisitor buildVisitor(@NotNull final ProblemsHolder holder, boolean isOnTheFly) {
        return new JavaElementVisitor() {

            /**
             *  This string defines the short message shown to a user signaling the inspection
             *  found a problem. It reuses a string from the inspections bundle.
             */
            @NonNls
            private static final String NO_PLACE_HOLDER_IN_FILE = "No placeholder in sql for %s";

            @NonNls
            private static final String MISSING_PLACE_HOLDERS_IN_PARAMS = "Missing the following placeholders in params:\n %s";

            @Override
            public void visitCallExpression(PsiCallExpression callExpression) {
                super.visitCallExpression(callExpression);
                if (!parsableSql(callExpression)) {
                    return;
                }
                PsiElement firstChild = callExpression.getFirstChild();
                loadSql((PsiMethodCallExpression) firstChild.getParent())
                        .map(sql -> Arrays.asList(sql.split(PLACE_HOLDER_SEPARATOR_REGEX)))
                        .map(this::toPlaceHolders)
                        .ifPresent(placeHolders -> {
                            final boolean singleTenantDbAccess = isSingleTenantDbAccess(callExpression);
                            if (singleTenantDbAccess) {
                                placeHolders.remove("companyId");
                            }
                            markProblems(firstChild, placeHolders, singleTenantDbAccess);
                        });
            }

            @NotNull
            private List<String> toPlaceHolders(List<String> sqlParts) {
                return sqlParts.stream()
                        .filter(part -> part.startsWith(":") && !part.startsWith("::"))
                        .map(this::toPlaceHolder)
                        .distinct()
                        .collect(Collectors.toList());
            }

            private boolean isSingleTenantDbAccess(PsiCallExpression callExpression) {
                final PsiElement statementElement = callExpression.findElementAt(0);
                if (statementElement != null && statementElement.getContext() instanceof PsiReferenceExpression) {
                    final PsiElement resolveStatementElement = ((PsiReferenceExpression) statementElement.getContext()).resolve();
                    if (resolveStatementElement instanceof PsiParameter) {
                        return lookupSingleTenantOnCallReferences(callExpression);
                    }
                }
                return lookupSingleTenantOnParent(callExpression) || lookupSingleTenantOnChild(callExpression);
            }

            private boolean lookupSingleTenantOnCallReferences(PsiCallExpression callExpression) {
                // First see the statement element comes from a method parameter...

                PsiMethod method = PsiTreeUtil.getParentOfType(callExpression, PsiMethod.class);
                if (method == null) {
                    return false;
                }

                final Collection<PsiReference> all = MethodReferencesSearch.search(
                        method, ProjectScope.getAllScope(callExpression.getProject()), true)
                        .findAll();
                return all.stream().allMatch(this::callerIsSingleTenant);
            }

            private boolean callerIsSingleTenant(PsiReference psiReference) {
                final PsiCallExpression psiCallExpression = PsiTreeUtil.getParentOfType(psiReference.getElement(), PsiCallExpression.class);
                if (psiCallExpression != null && psiCallExpression.getArgumentList() != null
                        && !psiCallExpression.getArgumentList().isEmpty()) {
                    final PsiElement[] children = psiCallExpression.getArgumentList().getChildren();
                    final boolean hasCompany = Stream.of(children)
                            .filter(psiElement -> psiElement instanceof PsiMethodCallExpression)
                            .anyMatch(psiElement -> lookupSingleTenantOnParent((PsiCallExpression) psiElement));
                    return hasCompany || lookupSingleTenantOnCallReferences(psiCallExpression);

                }
                return false;
            }

            private boolean lookupSingleTenantOnParent(PsiCallExpression callExpression) {
                // Lookup on expression parents
                PsiElement parent = callExpression;
                while (!(parent instanceof PsiClass)) {
                    if (parent instanceof PsiMethodCallExpression) {
                        if (parent.getFirstChild() != null && parent.getFirstChild().getLastChild() != null) {
                            final PsiElement potentialCompanyChild = parent.getFirstChild().getLastChild();
                            if (potentialCompanyChild.getText().equals("company")) {
                                return true;
                            }
                        }
                    }
                    parent = parent.getParent();
                }
                return false;
            }

            private boolean lookupSingleTenantOnChild(PsiCallExpression callExpression) {
                PsiElement firstChild = callExpression.getFirstChild();
                while (firstChild != null) {
                    final PsiElement lastChild = firstChild.getLastChild();
                    if (lastChild instanceof PsiIdentifier && lastChild.getText().equals("company")) {
                        return true;
                    }
                    firstChild = firstChild.getFirstChild();
                }
                return false;
            }

            private void markProblems(PsiElement firstChild, List<String> placeHolders, boolean singleTenantDbAccess) {
                Set<String> matchedParams = new HashSet<>();
                PlaceHolderQuickFix[] placeHolderQuickFixes = placeHolders.stream()
                        .map(PlaceHolderQuickFix::new)
                        .toArray(PlaceHolderQuickFix[]::new);
                PsiElement parent = firstChild.getParent().getParent();
                boolean checkMissingInParams = false;
                while (!(parent instanceof PsiClass)) {
                    if (parent instanceof PsiMethodCallExpression) {
                        PsiElement lastChild = ((PsiMethodCallExpression) parent).getMethodExpression()
                                .getLastChild();
                        if (isParam(lastChild)) {
                            PsiElement child = ((PsiMethodCallExpression) parent)
                                    .getArgumentList()
                                    .getChildren()[1];
                            if (child instanceof PsiLiteralExpression &&
                                    child.getNode().getElementType() instanceof JavaLiteralExpressionElementType
                                    && child.getText().startsWith("\"")) {
                                checkMissingInParams = true;
                                String param = child.getText().replace("\"", "");
                                if (param.equals("companyId") && singleTenantDbAccess) {
                                    holder.registerProblem(child,
                                            String.format("Remove redundant %s", param),
                                            ProblemHighlightType.WARNING,
                                            new RemoveParamQuickFix(param));
                                    parent = parent.getParent();
                                    continue;
                                }
                                System.out.print(String.format("Looking if :%s exists... ", param));
                                boolean matches = placeHolders.contains(param);
                                if (!matches) {
                                    holder.registerProblem(child,
                                            String.format(NO_PLACE_HOLDER_IN_FILE, param),
                                            placeHolderQuickFixes);
                                } else {
                                    matchedParams.add(param);
                                }
                                System.out.print(matches);
                                System.out.println();
                            }
                        }
                    }
                    parent = parent.getParent();
                }

                if (checkMissingInParams) {
                    markMissingPlaceHoldersInParams(firstChild, placeHolders, matchedParams);
                }
            }

            private boolean isParam(PsiElement lastChild) {
                return lastChild != null && (lastChild.getText().equals("param") ||
                        lastChild.getText().equals("paramNull") || lastChild.getText().equals("paramArray"));
            }

            private void markMissingPlaceHoldersInParams(PsiElement firstChild, List<String> placeHolders, Set<String> matchedParams) {
                List<String> noneExistingParams = placeHolders.stream()
                        .filter(ph -> !matchedParams.contains(ph))
                        .distinct()
                        .collect(Collectors.toList());
                if (!noneExistingParams.isEmpty()) {
                    PsiElement parent = firstChild.getParent();
                    Set<String> lastChildTexts = new HashSet<>();
                    while (parent != null && !(parent instanceof PsiFile)) {
                        final PsiElement lastChild = parent.getLastChild();
                        if ((lastChild instanceof PsiIdentifier) && (
                                lastChild.getText().startsWith("batchUpdate") ||
                                        lastChild.getText().startsWith("params"))) {
                            System.out.println("Has dynamic params, skipping missed check on " + firstChild);
                            return;
                        }
                        if ((lastChild instanceof PsiIdentifier)) {
                            lastChildTexts.add(lastChild.getText());
                        }
                        parent = parent.getParent();
                    }

                    boolean registerProblem = lastChildTexts.stream()
                            .anyMatch(childText -> childText.startsWith("query") || childText.equals("update"));
                    if (registerProblem) {
                        holder.registerProblem(firstChild,
                                String.format(MISSING_PLACE_HOLDERS_IN_PARAMS,
                                        String.join("\n", noneExistingParams)));
                    } else {
                        System.out.println("Has dynamic params, skipping missed check on " + firstChild);
                    }
                }
            }

            private boolean parsableSql(PsiCallExpression callExpression) {
                if (callExpression.getParent() != null) {
                    PsiElement lastChild = callExpression.getParent().getLastChild();
                    if (lastChild != null && lastChild.getText().startsWith("batchUpdate")) {
                        return false;
                    }
                }
                PsiElement firstChild = callExpression.getFirstChild();
                return firstChild != null &&
                        (firstChild.getText().endsWith("statement") ||
                                firstChild.getText().endsWith("statements") ||
                                firstChild.getText().endsWith("sql") ||
                                firstChild.getText().endsWith("sqls") ||
                                firstChild.getText().endsWith("sqlNoLogging")) &&
                        callExpression instanceof PsiMethodCallExpression &&
                        isValidFilePath((PsiMethodCallExpression) callExpression);
            }

            private String toPlaceHolder(String part) {
                String actualPart = part.substring(1);
                int indexOfJsonIdentifier = actualPart.toLowerCase().indexOf("::");
                return indexOfJsonIdentifier > -1 ? actualPart.substring(0, indexOfJsonIdentifier) : actualPart;
            }

            private Optional<String> loadSql(PsiMethodCallExpression psiMethodCallExpression) {
                PsiElement child = psiMethodCallExpression.getArgumentList().getChildren()[1];
                String path = child.getText().replace("\"", "");
                final PsiFile containingFile = child.getContainingFile();
                final Module module = ModuleUtil.findModuleForFile(containingFile);
                // First check in main
                VirtualFile sqlFile = resolveSqlFile(module, containingFile, path, "main");

                // If not found and file belongs to test then check in test folder
                if (sqlFile == null && containingFile.getVirtualFile().getCanonicalPath().contains("test")) {
                    sqlFile = resolveSqlFile(module, containingFile, path, "test");
                }

                // Case both paths not resolved register file does not exists problem
                if (sqlFile == null || !sqlFile.exists()) {
                    holder.registerProblem(child,
                            "Sql file does not exists");
                    return Optional.empty();
                }

                FileDocumentManager fileDocumentManager = FileDocumentManager.getInstance();
                return Optional.ofNullable(fileDocumentManager.getDocument(sqlFile))
                        .map(Document::getText)
                        .map(this::filterOutComments);
            }

            private String filterOutComments(String sql) {
                final String[] lines = sql.split("\n");
                StringBuilder sb = new StringBuilder();
                for (int i = 0; i < lines.length; i++) {
                    int indexOfComment = lines[i].indexOf("--");
                    if (indexOfComment > -1) {
                        sb.append(lines[i], 0, indexOfComment).append('\n');
                    } else {
                        sb.append(lines[i]).append('\n');
                    }
                }
                return sb.toString();
            }
        };
    }

    @Nullable
    private VirtualFile resolveSqlFile(Module module, PsiFile containingFile, String path, String resourceContainer) {
        VirtualFile sqlFile = module.getModuleFile().getParent().findFileByRelativePath("src/" + resourceContainer
                + "/resources/" + path);
        if (sqlFile == null) {
            final HashSet<Module> modules = Sets.newHashSet();
            ModuleUtil.getDependencies(Objects.requireNonNull(ModuleUtil.findModuleForFile(containingFile)), modules);
            sqlFile = modules.stream()
                    .map(currentModule -> currentModule.getModuleFile().getParent())
                    .map(directory -> directory.findFileByRelativePath("src/" + resourceContainer + "/resources/" + path))
                    .filter(Objects::nonNull)
                    .findFirst()
                    .orElse(null);
        }

        return sqlFile;
    }

    private boolean isValidFilePath(PsiMethodCallExpression psiMethodCallExpression) {
        PsiElement child = psiMethodCallExpression.getArgumentList().getChildren()[1];
        final String text = child.getText();
        if (!(text.startsWith("\"") || text.endsWith("\""))) {
            return false;
        }
        String path = text.substring(1, text.length() - 1);
        return path.matches("[^\\\"]+/[^\\/]+$");
    }

    private static class RemoveParamQuickFix implements LocalQuickFix {

        private final String param;

        public RemoveParamQuickFix(String param) {
            this.param = param;
        }

        @Nls(capitalization = Nls.Capitalization.Sentence)
        @NotNull
        @Override
        public String getFamilyName() {
            return "Remove redundant " + param;
        }

        @Override
        public void applyFix(@NotNull Project project, @NotNull ProblemDescriptor problemDescriptor) {
            PsiLiteralExpression psiLiteralExpression = (PsiLiteralExpression) problemDescriptor.getPsiElement();
            psiLiteralExpression.getParent().getPrevSibling().getLastChild().getPrevSibling().getPrevSibling().delete();
            psiLiteralExpression.getParent().getPrevSibling().getLastChild().delete();
            psiLiteralExpression.getParent().delete();
        }
    }

    /**
     * This class provides a solution to inspection problem expressions by
     * replacing the non existing place holder with an existing one specified in the constructor
     */
    private static class PlaceHolderQuickFix implements LocalQuickFix {

        private final String placeHolder;

        public PlaceHolderQuickFix(String placeHolder) {
            this.placeHolder = placeHolder;
        }

        /**
         * Returns a partially localized string for the quick fix intention.
         * Used by the test code for this plugin.
         *
         * @return Quick fix short name.
         */
        @NotNull
        @Override
        public String getName() {
            return placeHolder;
        }

        /**
         * This method manipulates the PSI tree to replace 'a==b' with 'a.equals(b)
         * or 'a!=b' with '!a.equals(b)'
         *
         * @param project    The project that contains the file being edited.
         * @param descriptor A problem found by this inspection.
         */
        public void applyFix(@NotNull Project project, @NotNull ProblemDescriptor descriptor) {
            try {
                PsiLiteralExpression psiLiteralExpression = (PsiLiteralExpression) descriptor.getPsiElement();
                PsiElementFactory factory = JavaPsiFacade.getInstance(project).getElementFactory();
                PsiExpression expressionFromText = factory.createExpressionFromText("\"" + placeHolder + "\"", null);
                psiLiteralExpression.replace(expressionFromText);
            } catch (IncorrectOperationException e) {
                LOG.error(e);
            }
        }

        @NotNull
        public String getFamilyName() {
            return getName();
        }
    }

}
