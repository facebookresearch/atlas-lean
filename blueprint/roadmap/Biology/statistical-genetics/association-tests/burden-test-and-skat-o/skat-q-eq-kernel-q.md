# SKAT is the kernel score statistic of the SKAT kernel

For a real `n × q` covariate matrix `X`, a real `n × n` matrix `V`, a real `n × m` genotype matrix
`G`, variant weights `w ∈ ℝᵐ` and every phenotype `y ∈ ℝⁿ`, the
[SKAT statistic](../skat-variance-component-test/skat-q.md) with weights `w`,
`(V⁻¹ (y - X α̂))ᵀ K (V⁻¹ (y - X α̂))` with `α̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`, is the
[kernel score statistic](kernel-q.md) of the
[SKAT kernel](../skat-variance-component-test/skat-kernel.md) `K = G diag(w) Gᵀ`:

`Q_SKAT(y) = (P y)ᵀ G diag(w) Gᵀ (P y)`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection. No condition is imposed on `X`,
`V`, `G` or `w`; the inverse of a singular matrix is taken to be `0`.
