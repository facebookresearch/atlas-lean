# The burden statistic is at most m times SKAT with squared weights

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G` of `m` variants, variant weights `a ∈ ℝᵐ` and every phenotype `y ∈ ℝⁿ`, the Cauchy–Schwarz
inequality gives

`Q_B(y) = (∑ⱼ aⱼ Sⱼ(y))² ≤ m ∑ⱼ aⱼ² Sⱼ(y)²`:

the [burden statistic](burden-q.md) is at most `m` times the
[SKAT statistic](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/skat-q-eq-sum-variant-score.md) with weights
`wⱼ = aⱼ²`, which is `∑ⱼ wⱼ Sⱼ(y)²`. Here `Sⱼ(y) = gⱼᵀ P y` are the single-variant scores, `gⱼ`
the column of `G` for variant `j`, and `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null
projection, the inverse of a singular matrix being taken to be `0`. With no variants, `m = 0`, both
sides are `0`.
