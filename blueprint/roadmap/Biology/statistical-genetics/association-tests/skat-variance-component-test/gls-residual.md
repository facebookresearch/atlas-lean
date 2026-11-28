# Null-model GLS residual

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V` and a phenotype `y ∈ ℝⁿ`, the
null-model GLS residual is

`y - X α̂`, `α̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`,

where `α̂ = B y` with `B` the
[generalized least-squares matrix](../../../../Probability/linear-models-multivariate/generalized-least-squares/gls-matrix.md),
with the convention that the inverse of a singular matrix is `0`. So the residual is `y` itself when
`V` or `Xᵀ V⁻¹ X` is singular. When `V` is positive definite and `Xᵀ V⁻¹ X` is invertible, `α̂` is
the GLS estimate of `α` in `y = X α + e` with `Cov(e) = V`.
