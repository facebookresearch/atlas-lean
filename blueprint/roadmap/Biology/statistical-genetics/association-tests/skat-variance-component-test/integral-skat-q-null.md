# The null mean of the SKAT statistic is tr(K P)

Let `V` be a positive definite real `n × n` matrix and `X` a real `n × q` covariate matrix such that
`Xᵀ V⁻¹ X` is invertible, and let `α ∈ ℝ^q`, `G` a real `n × m` genotype matrix and `w` real
weights. Under the null hypothesis `y ~ N(X α, V)`, the Gaussian law with mean `X α` in the span of
the covariates and covariance `V`, the [SKAT statistic](skat-q.md) has mean

`𝔼₀ Q = tr(K P)`,

with `P` the [null projection](proj-p.md) and `K` the [SKAT kernel](skat-kernel.md). So the centred
statistic `Q - tr(K P)` has null mean `0`, and the weights of the
[null law](map-skat-q-multivariate-gaussian.md) `∑ⱼ λⱼ χ²₁` sum to `tr(K P)`.
