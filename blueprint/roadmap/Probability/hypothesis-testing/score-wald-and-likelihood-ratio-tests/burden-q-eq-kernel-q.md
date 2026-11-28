# The burden statistic is the kernel statistic of the burden kernel

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G`, variant weights `a ∈ ℝᵐ` and every phenotype `y ∈ ℝⁿ`, the [burden statistic](burden-q.md) is
the [kernel score statistic](kernel-q.md) of the [burden kernel](burden-kernel.md) `K_B = C Cᵀ`,
`C = G a`:

`Q_B(y) = (Cᵀ P y)² = (P y)ᵀ C Cᵀ (P y)`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the inverse of a singular
matrix being taken to be `0`.
