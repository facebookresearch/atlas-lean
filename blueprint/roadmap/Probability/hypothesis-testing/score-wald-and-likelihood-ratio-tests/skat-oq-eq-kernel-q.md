# The SKAT-O statistic is the kernel statistic of the SKAT-O kernel

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G`, variant weights `a ∈ ℝᵐ`, every real number `ρ` and every phenotype `y ∈ ℝⁿ`, the
[SKAT-O statistic](skat-oq.md) is the [kernel score statistic](kernel-q.md) of the
[SKAT-O kernel](skat-okernel.md):

`(1 - ρ) Q_S(y) + ρ Q_B(y) = (P y)ᵀ K_ρ (P y)`, with `K_ρ = G diag(a) R_ρ diag(a) Gᵀ`,

where `Q_S` is SKAT with weights `wⱼ = aⱼ²`, `Q_B` the burden statistic, `R_ρ = (1 - ρ) I + ρ 𝟙 𝟙ᵀ`
and `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` the null projection, the inverse of a singular matrix
being taken to be `0`.
