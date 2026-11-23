# Trace of the cube of the LD matrix

For a real `N × M` genotype matrix `X` with [in-sample LD matrix](ld-matrix.md) `R`, the third LD
moment is

`T = ∑_j ∑_l ∑_k R_jl R_jk R_lk = tr R³`,

where the last equality uses the symmetry of `R`. With the convention `x / 0 = 0`, `T = 0` when
`N = 0`.
