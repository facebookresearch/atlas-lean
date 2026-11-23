# In-sample LD matrix

For a real `N × M` genotype matrix `X`, the in-sample LD matrix is the real `M × M` matrix `R` with
entries

`R_jk = (1 / N) ∑_i X_ij X_ik`,

the [normalized cross products](../ld-score-regression/ld-corr.md) of the markers, with the
convention `x / 0 = 0`: `R = 0` when `N = 0`. It is symmetric. For a
[standardized](../ld-score-regression/is-standardized.md) genotype matrix with `N > 0` it is the
sample correlation matrix of the markers.
