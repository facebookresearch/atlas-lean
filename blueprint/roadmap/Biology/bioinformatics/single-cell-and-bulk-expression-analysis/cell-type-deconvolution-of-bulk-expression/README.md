# Cell-type deconvolution of bulk expression

A bulk expression profile is modelled as a nonnegative mixture of cell-type signature profiles. Recovering the cell-type fractions from a signature matrix is an overdetermined nonnegative regression, solved by constrained least squares (with room for an uncharacterized remainder and an mRNA-content correction) or by support vector regression, with a Monte Carlo null for the goodness of fit. Once the fractions are known, one representative profile per cell type is again an overdetermined nonnegative least squares problem, while sample-specific, cell-type-specific expression is underdetermined and needs extra constraints.

- [Linear mixture model for cell type fractions](linear-mixture-model-for-cell-type-fractions.md)
- [Constrained least-squares deconvolution with an uncharacterized remainder](constrained-least-squares-deconvolution-with-an-uncharacterized-remainder.md)
- [Nu-support vector regression deconvolution of cell-type fractions](nu-support-vector-regression-deconvolution-of-cell-type-fractions.md)
- [Monte Carlo null for the goodness of fit of a deconvolution](monte-carlo-null-for-the-goodness-of-fit-of-a-deconvolution.md)
- [Group-mode expression purification by nonnegative least squares](group-mode-expression-purification-by-nonnegative-least-squares.md)
- [High-resolution expression purification is an underdetermined decomposition](high-resolution-expression-purification-is-underdetermined.md)
