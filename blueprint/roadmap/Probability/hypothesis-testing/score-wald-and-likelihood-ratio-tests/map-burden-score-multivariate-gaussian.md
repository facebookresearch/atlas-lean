# Burden score of a Gaussian phenotype with mean X α is centred Gaussian

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where `V⁻¹` is the inverse of `V`, or `0` when `V` is singular. Let `V'` be a positive
semidefinite real `n × n` matrix and `α ∈ ℝ^q`. If the phenotype `y` is Gaussian with mean `X α`
and covariance `V'`, then for every real `n × m` genotype matrix `G` and variant weights `a ∈ ℝᵐ`
the [burden score](burden-score.md) `B(y) = Cᵀ P y`, `C = G a`, is centred Gaussian with variance

`(Pᵀ C)ᵀ V' (Pᵀ C)`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection. The mean is `0` because
`P X = 0`; the variance is nonnegative because `V'` is positive semidefinite, and when it is `0` the
law is the point mass at `0`.
