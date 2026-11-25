# Kernel statistics of Gaussian phenotypes with mean X α are χ² mixtures

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where `V⁻¹` is the inverse of `V`, or `0` when `V` is singular. Let `K` be a symmetric
real `n × n` kernel, `α ∈ ℝ^q` and `V'` any real `n × n` matrix. If the phenotype `y` has law
`N(X α, V')`, the [kernel score statistic](kernel-q.md) `Q_K(y) = (P y)ᵀ K (P y)` has the weighted
chi-square law

`Q_K ~ ∑ⱼ λⱼ χ²₁`,

the law of `∑ⱼ λⱼ ξⱼ²` for independent standard normal variables `ξ₁, …, ξₙ`, where
`λ₁, …, λₙ` are the eigenvalues, with multiplicity, of the symmetric
[mixture-weight matrix](kernel-mixture-matrix.md) `A = (P V'^{1/2})ᵀ K (P V'^{1/2})` and
`P = V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹` is the null projection.

Here `N(X α, V')` is the image of the standard Gaussian law on `ℝⁿ` under `z ↦ X α + V'^{1/2} z`.
When `V'` is positive semidefinite, `V'^{1/2}` is its positive semidefinite square root and
`N(X α, V')` is the Gaussian law with mean `X α` and covariance `V'`. For any other `V'`, `V'^{1/2}`
is taken to be `0`: then `N(X α, V')` is the point mass at `X α`, every `λⱼ` is `0`, and both laws
are the point mass at `0`. The weights are
[nonnegative](eigenvalues-kernel-mixture-matrix-nonneg.md) when `K` is positive semidefinite, but
can be negative for other symmetric kernels. Taking `V' = V` gives the null law; the
[law of the SKAT statistic](../../../Biology/statistical-genetics/association-tests/skat-variance-component-test/map-skat-q-multivariate-gaussian.md) is
the special case `K = G diag(w) Gᵀ`.
