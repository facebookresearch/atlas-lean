# The burden statistic has null mean Cᵀ P C

Let `V` be a positive definite real `n × n` matrix, `X` a real `n × q` covariate matrix with
`Xᵀ V⁻¹ X` invertible, and `α ∈ ℝ^q`. Under the null model, in which the phenotype `y` is Gaussian
with mean `X α` and covariance `V`, the expected value of the [burden statistic](burden-q.md) is

`𝔼₀ Q_B = Cᵀ P C`,

for every real `n × m` genotype matrix `G` and variant weights `a ∈ ℝᵐ`, where `C = G a` and
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection. The statistic is integrable, its
null law being [`(Cᵀ P C) χ²₁`](map-burden-q-null.md).
