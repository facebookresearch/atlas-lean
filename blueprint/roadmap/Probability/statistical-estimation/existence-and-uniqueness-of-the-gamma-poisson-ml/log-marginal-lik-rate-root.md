# The log likelihood along the rate root is the profile plus a constant

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`,
observed at a common size factor `σ > 0`, and let `ℓ(a, b)` be their
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. Assume `M > 0`. For every `a > 0`,
`ℓ(a, σ a / M) = L(a) + ∑ᵢ (kᵢ log M - log kᵢ!)`, where `L` is the
[profile log likelihood](profile-log-lik.md)
`L(a) = ∑ᵢ ∑_{j<kᵢ} log (a + j) + n (a log a - (a + M) log (a + M))`. The added constant depends on
the counts only, not on `a` or `σ`.
