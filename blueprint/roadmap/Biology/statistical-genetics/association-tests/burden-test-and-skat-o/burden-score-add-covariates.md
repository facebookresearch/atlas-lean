# For invertible Xᵀ V⁻¹ X the burden score ignores covariate effects

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where `V⁻¹` is the inverse of `V`, or `0` when `V` is singular. Then for every real
`n × m` genotype matrix `G`, variant weights `a ∈ ℝᵐ`, covariate effects `α ∈ ℝ^q` and phenotype
`y ∈ ℝⁿ`, the [burden score](burden-score.md) satisfies

`B(X α + y) = B(y)`:

since `B(y) = Cᵀ P y` with `C = G a`, this follows from `P X = 0` for the null projection
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`.
