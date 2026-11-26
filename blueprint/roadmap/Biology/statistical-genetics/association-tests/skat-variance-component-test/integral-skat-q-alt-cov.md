# Mean of the SKAT statistic along the variance-component alternative

Let `V` be a positive definite real `n × n` matrix and `X` a real `n × q` covariate matrix such that
`Xᵀ V⁻¹ X` is invertible, `G` a real `n × m` genotype matrix, `w` nonnegative weights, `τ ≥ 0` and
`α ∈ ℝ^q`. If `y` has the Gaussian law `N(X α, V + τ K)` with mean `X α` in the span of the
covariates and the [alternative covariance](alt-cov.md), the [SKAT statistic](skat-q.md) has mean

`𝔼_τ Q = tr(K P) + τ tr(K P K Pᵀ)`,

with `K` the [SKAT kernel](skat-kernel.md) and `P` the [null projection](proj-p.md): an affine
function of `τ ≥ 0` whose slope `tr(K P K Pᵀ)` is
[nonnegative](trace-skat-kernel-mul-proj-p-nonneg.md).
