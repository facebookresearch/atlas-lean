# The profile log likelihood has derivative the profile shape score

For a finite family of counts `k₁, …, kₙ` with
[sample mean](../likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` (so `M ≥ 0`)
and every `a > 0`, the [profile log likelihood](profile-log-lik.md)
`L(x) = ∑ᵢ ∑_{j<kᵢ} log (x + j) + n (x log x - (x + M) log (x + M))` is differentiable at `a`, with
derivative the
[profile shape score](../likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md)
`∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n (log (a + M) - log a)`.
