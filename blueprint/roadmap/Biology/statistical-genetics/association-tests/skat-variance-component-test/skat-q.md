# SKAT variance-component score statistic

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G`, real weights `w` and a phenotype `y ∈ ℝⁿ`, the SKAT statistic is

`Q = (V⁻¹ r)ᵀ K (V⁻¹ r)`,

where `r = y - X α̂` is the [null-model GLS residual](gls-residual.md) and `K = G diag(w) Gᵀ` the
[SKAT kernel](skat-kernel.md), with the convention that the inverse of a singular matrix is `0`. In
particular `Q = 0` when `V` is singular. For symmetric `V` it is `rᵀ V⁻¹ K V⁻¹ r`. With `V = σ² I`,
`σ² > 0`, and `Xᵀ X` invertible, it is `σ⁻⁴` times the statistic `(y - μ̂)ᵀ K (y - μ̂)` of Wu et al.
(2011, eq. (3)), `μ̂` the least-squares fit of the null model.
