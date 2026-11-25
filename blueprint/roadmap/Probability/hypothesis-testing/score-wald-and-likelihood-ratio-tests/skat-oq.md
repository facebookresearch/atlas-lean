# SKAT-O statistic, an affine combination of SKAT and burden statistics

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G`, variant weights `a ∈ ℝᵐ`, a real number `ρ` and a phenotype `y ∈ ℝⁿ`, the SKAT-O statistic is

`Q_ρ(y) = (1 - ρ) Q_S(y) + ρ Q_B(y)`,

where `Q_S` is the [SKAT statistic](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/skat-q.md) with weights
`wⱼ = aⱼ²` and `Q_B` the [burden statistic](burden-q.md) with weights `a`, both built from the null
projection `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`, the inverse of a singular matrix being taken to be
`0`. It is defined for every real `ρ`; for `ρ ∈ [0, 1]`, the range SKAT-O uses, it is a convex
combination of the two statistics, equal to SKAT at [`ρ = 0`](skat-oq-zero.md) and to the burden
statistic at [`ρ = 1`](skat-oq-one.md).
