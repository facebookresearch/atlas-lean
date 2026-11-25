# Posterior mean of the expression rate

For real numbers `a, b, s` and `k ∈ ℕ`, the posterior mean is `(a + k) / (b + s)`, with the
convention `x / 0 = 0` when `b + s = 0`. For `a > 0`, `b > 0` and `s ≥ 0` it is the
[mean of the posterior law](integral-id-posterior.md) `Gamma(a + k, b + s)` of the rate `λ` after
observing `k ~ Po(s λ)` under the prior `λ ~ Gamma(a, b)`.
