# Exactly one joint MLE at a common size factor, Pearson form

Let `k₁, …, kₙ` (`n ≥ 1`) be counts observed at a common size factor `σ > 0`, with
[log marginal likelihood](../likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
`ℓ(a, b)` in the shape `a` and the rate `b`, and assume the Pearson form of the overdispersion
condition, `∑ᵢ (kᵢ - σ μ̂)² > ∑ᵢ kᵢ`, where `μ̂ = (∑ᵢ kᵢ) / (n σ)` is the
[pooled Poisson rate](pooled-mean.md) (so `σ μ̂ = M`, the
[sample mean](../likelihood-equations-and-efficiency-of-the-gamma/count-mean.md)). It is equivalent
to `M < V`, with `V` the
[biased sample variance](../likelihood-equations-and-efficiency-of-the-gamma/count-var.md)
([the condition at a common size factor](overdispersed-const-iff.md)). Then `ℓ` has exactly one
maximizer over `(0, ∞)²`: there is exactly one `(â, b̂)` with `â > 0`, `b̂ > 0` and
`ℓ(a, b) ≤ ℓ(â, b̂)` for every `a > 0` and `b > 0` (Levin and Reeds 1977, Theorem 2).
