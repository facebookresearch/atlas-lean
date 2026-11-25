# The mean of the SKAT statistic is smallest at τ = 0

Let `V` be a positive definite real `n × n` matrix and `X` a real `n × q` covariate matrix such that
`Xᵀ V⁻¹ X` is invertible, `G` a real `n × m` genotype matrix, `w` nonnegative weights, `τ ≥ 0` and
`α ∈ ℝ^q`. Then the mean of the [SKAT statistic](skat-q.md) under `y ~ N(X α, V)` is at most its
mean under `y ~ N(X α, V + τ K)`, both Gaussian laws with the same mean `X α` in the span of the
covariates, with `K` the [SKAT kernel](skat-kernel.md):

`𝔼₀ Q ≤ 𝔼_τ Q`.

So among `τ ≥ 0` the mean of `Q` is smallest at the boundary `τ = 0`: moving away from it can only
increase the mean of `Q`, and the test rejects for large `Q`.
