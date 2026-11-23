# The burden score is centred Gaussian under the null model

Let `V` be a positive definite real `n × n` matrix (the null covariance), `X` a real `n × q`
covariate matrix with `Xᵀ V⁻¹ X` invertible, and `α ∈ ℝ^q`. Under the null model, in which the
phenotype `y` is Gaussian with mean `X α` and covariance `V`, for every real `n × m` genotype matrix
`G` and variant weights `a ∈ ℝᵐ` the [burden score](burden-score.md) is centred Gaussian:

`B(y) = Cᵀ P y ~ N(0, Cᵀ P C)`, with `C = G a`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection. The variance `Cᵀ P C` is
[nonnegative](burden-var-nonneg.md); when it is `0` the law is the point mass at `0`.
