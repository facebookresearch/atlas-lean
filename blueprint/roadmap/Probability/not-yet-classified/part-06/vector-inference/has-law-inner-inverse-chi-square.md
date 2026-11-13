# Gaussian quadratic forms are chi-square

Let `S` be a symmetric positive definite
operator on a finite-dimensional real inner product space `E` of dimension `d ≥ 1`, and let
`V ~ N(0, S)`, i.e. `⟪V, t⟫ ~ N(0, ⟪S t, t⟫)` for every `t`. Then
`⟪S⁻¹ V, V⟫ ~ χ²_d`.

The proof diagonalizes `S` in an orthonormal eigenbasis (`LinearMap.IsSymmetric.eigenvectorBasis`),
whitens `V` to a standard Gaussian vector `W`, and applies
`ProbabilityTheory.stdGaussian_map_sum_sq_inner`.
