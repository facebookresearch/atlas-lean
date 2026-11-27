# Profile log likelihood of the shape at a common size factor

For a finite family of counts `k₁, …, kₙ` with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and a real `a`,
the profile log likelihood is `L(a) = ∑ᵢ ∑_{j<kᵢ} log (a + j) + n (a log a - (a + M) log (a + M))`.
The logarithm is extended by `log 0 = 0` and `log x = log |x|` for `x < 0`; the intended domain is
`a > 0`, where every argument is positive.

For `n ≥ 1`, `M > 0`, a common size factor `σ > 0` and `a > 0`, the
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
`ℓ` at the rate `σ a / M` is `ℓ(a, σ a / M) = L(a) + ∑ᵢ (kᵢ log M - log kᵢ!)`
([the log likelihood along the rate root](log-marginal-lik-rate-root.md)). That rate maximizes
`ℓ(a, ·)` over `b > 0`
([the rate root is the global maximizer](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik-lt-of-rate-score-eq-zer.md)),
so `L` is the profile log likelihood of the shape up to an additive constant that depends on the
counts only. Its derivative is the
[profile shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md)
([derivative of the profile log likelihood](has-deriv-at-profile-log-lik.md)).
