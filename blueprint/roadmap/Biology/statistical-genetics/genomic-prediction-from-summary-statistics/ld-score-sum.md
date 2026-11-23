# Sum of the LD scores

For a real `N × M` genotype matrix `X` with [in-sample LD matrix](ld-matrix.md) `R`, the sum of the
[LD scores](../ld-score-regression/ld-score.md) is

`L = ∑_j ℓ_j = ∑_j ∑_k R_jk² = tr R²`,

where the last equality uses the symmetry of `R`. With the convention `x / 0 = 0`, `L = 0` when
`N = 0`.
