# If G a = 0 the null law of the burden score is the point mass at 0

Let `V` be a positive definite real `n × n` matrix, `X` a real `n × q` covariate matrix with
`Xᵀ V⁻¹ X` invertible, `α ∈ ℝ^q`, and let the real `n × m` genotype matrix `G` and the weights
`a ∈ ℝᵐ` have a vanishing collapsed genotype, `C = G a = 0` (for example when no individual carries
a minor allele at any variant of nonzero weight). Under the null model, in which the phenotype `y`
is Gaussian with mean `X α` and covariance `V`, the law of the [burden score](burden-score.md) is
the point mass at `0`: its null variance `Cᵀ P C` is `0`, and indeed `B(y) = Cᵀ P y = 0` for every
`y`, where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection.
