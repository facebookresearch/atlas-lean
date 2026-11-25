# Variance-component score statistic of a general kernel

For a real `n × q` covariate matrix `X`, real `n × n` matrices `V` (the null covariance) and `K`
(the kernel), and a phenotype `y ∈ ℝⁿ`, the kernel score statistic is

`Q_K(y) = (P y)ᵀ K (P y)`,

where `P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the
[null projection](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/proj-p.md). Any real matrices are allowed; the
inverse of a singular matrix is taken to be `0`. Since `P y = V⁻¹ (y - X α̂)` with
`α̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`, for symmetric `V` the statistic equals
`(y - X α̂)ᵀ V⁻¹ K V⁻¹ (y - X α̂)`. When `V` is positive definite and `Xᵀ V⁻¹ X` is invertible, `α̂`
is the
[generalized least-squares fit](../../linear-models-multivariate/generalized-least-squares/gls-matrix.md)
of the null model `y = X α + e`, `Cov e = V`, and `Q_K` is the variance-component score statistic
for the kernel `K`; for `V = σ² I`, `σ² > 0`, it is `σ⁻⁴` times the statistic `(y - μ̂)ᵀ K (y - μ̂)`
of Lee, Wu and Lin (2012), `μ̂` the least-squares fit of the null model.
[SKAT](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/skat-q-eq.md) with weights `w`, the [burden test](burden-q-eq-kernel-q.md) with
weights `a` and [SKAT-O](skat-oq-eq-kernel-q.md) are the kernels `G diag(w) Gᵀ`, `(G a)(G a)ᵀ` and
`G diag(a) R_ρ diag(a) Gᵀ` of a genotype matrix `G`.
