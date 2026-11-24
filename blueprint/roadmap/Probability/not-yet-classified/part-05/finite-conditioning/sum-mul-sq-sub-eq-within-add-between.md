# Total-variance decomposition

The variance of `Y` is the mean within-cell variance
plus the variance of the cell means under the cell law,
`Var(Y) = E[Var(Y | G)] + Var(E[Y | G])`. The centre of the second term is the cell-law mean
of the cell means, which equals `E[Y]` by `sum_mul_eq_sum_cellMass_mul_cellMean`.
