# At most one profile zero at a common size factor, Pearson form

Let `k₁, …, kₙ` (`n ≥ 1`) be counts observed at a common size factor `σ > 0`, with
[log marginal likelihood](../likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
`ℓ(a, b)` in the shape `a` and the rate `b`, and assume the Pearson form of the overdispersion
condition, `∑ᵢ (kᵢ - σ μ̂)² > ∑ᵢ kᵢ`, where `μ̂ = (∑ᵢ kᵢ) / (n σ)` is the
[pooled Poisson rate](pooled-mean.md) (so `σ μ̂ = M`, the
[sample mean](../likelihood-equations-and-efficiency-of-the-gamma/count-mean.md)). It is equivalent
to `M < V`, with `V` the
[biased sample variance](../likelihood-equations-and-efficiency-of-the-gamma/count-var.md)
([the condition at a common size factor](overdispersed-const-iff.md)). Then the
[profile shape score along the rate root](profile-shape-score-varying.md) has at most one zero in
`(0, ∞)`: if `a > 0`, `a' > 0` and both are zeros, then `a = a'` (Levin and Reeds 1977, Theorem 2).
The condition matters: for `σ = 1` and all counts `0` the profile vanishes at every `a > 0`.
