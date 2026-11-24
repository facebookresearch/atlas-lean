# Boundary diag2n prod eq reindex diagonal Units Hom product One Diagonal

Boundary `diag2n` product equals reindexed product-one diagonal.
For `u : Fin n → Fˣ`, `diag2n (castSucc_ne_last i)` has `u i` at
`castSucc i` and `(u i)⁻¹` at `last`. Product is diagonal with `u i`
at `castSucc i` and `(∏ u)⁻¹` at `last`, equal to
`diagonalUnitsHom (productOneDiagonal u)` reindexed by `finSumFinEquiv`.
Uniform for `n = 0` and char 2. Orientation:
`∏ i, toGL (diag2n ...) = reindex finSumFinEquiv (diagonalUnitsHom ...)`.
