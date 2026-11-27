# Quadratic form of the null projection at the collapsed genotype

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G` and variant weights `a ∈ ℝᵐ`, this is the number

`Cᵀ P C`, with `C = G a`,

where `Cᵢ = ∑ⱼ Gᵢⱼ aⱼ` is the `a`-weighted sum of the minor-allele counts of individual `i` and
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the
[null projection](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/proj-p.md), the inverse of a singular matrix being
taken to be `0`. When `V` is positive definite and `Xᵀ V⁻¹ X` is invertible, it is
[nonnegative](burden-var-nonneg.md) and it is the variance of the [burden score](burden-score.md)
under the null model in which `y` is Gaussian with mean `X α` and covariance `V`
([null law of the burden score](map-burden-score-null.md)). For other `V` it need not be a
variance: with no covariates and `V = -I` it equals `-Cᵀ C`.
