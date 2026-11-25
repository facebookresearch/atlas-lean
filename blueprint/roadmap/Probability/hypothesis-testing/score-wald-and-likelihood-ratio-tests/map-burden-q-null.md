# The burden statistic is a scaled chi-square under the null model

Let `V` be a positive definite real `n × n` matrix, `X` a real `n × q` covariate matrix with
`Xᵀ V⁻¹ X` invertible, and `α ∈ ℝ^q`. Under the null model, in which the phenotype `y` is Gaussian
with mean `X α` and covariance `V`, for every real `n × m` genotype matrix `G` and variant weights
`a ∈ ℝᵐ` the [burden statistic](burden-q.md) `Q_B(y) = B(y)²` has the one-term weighted chi-square
law

`Q_B ~ (Cᵀ P C) χ²₁`,

the law of `(Cᵀ P C) ξ²` for a standard normal variable `ξ`, where `C = G a` and
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection. When `Cᵀ P C = 0` this is the point
mass at `0`.
