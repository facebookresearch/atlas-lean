# The kernel statistic is linear in the kernel

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, real `n × n` kernels `K₁` and
`K₂`, real numbers `c₁` and `c₂`, and every phenotype `y ∈ ℝⁿ`, the
[kernel score statistic](kernel-q.md) `Q_K(y) = (P y)ᵀ K (P y)` satisfies

`Q_{c₁ K₁ + c₂ K₂}(y) = c₁ Q_{K₁}(y) + c₂ Q_{K₂}(y)`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection, the inverse of a singular
matrix being taken to be `0`.
