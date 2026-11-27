# Aitken's block identity

**Aitken's block identity** (Aitken 1934, (7)). Let `Σ_XX` be a symmetric `p × p` real
matrix with nonzero determinant, let `Σ_XY` be a `p × q` and `Σ_YY` a `q × q` real matrix, and
let `V` be any `p × p` real matrix (the selected covariance of `X`). Put `B = Σ_XYᵀ Σ_XX⁻¹`.
Then `V Bᵀ = V Σ_XX⁻¹ Σ_XY`, and
`B V Bᵀ + (Σ_YY - Σ_XYᵀ Σ_XX⁻¹ Σ_XY) = Σ_YY - Σ_XYᵀ (Σ_XX⁻¹ - Σ_XX⁻¹ V Σ_XX⁻¹) Σ_XY`.
So the regression-form selected covariance blocks, with the population regression coefficient `B`
and residual covariance `Σ_YY - Σ_XYᵀ Σ_XX⁻¹ Σ_XY`, are Aitken's blocks.

## Sources

- Aitken (1934), p. 109, equation (7).
