# Overdispersion gives a joint score root at any positive size factors

Let `k₁, …, kₙ` (`n ≥ 1`) be counts observed at positive size factors `s₁, …, sₙ`, and let `ℓ(a, b)`
be their
[log marginal likelihood](../likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. Let `μ̂ = (∑ᵢ kᵢ) / (∑ᵢ sᵢ)` be the
[pooled Poisson rate](pooled-mean.md) and `sᵢ μ̂` the fitted Poisson means. If the Pearson-type
excess `∑ᵢ (kᵢ - sᵢ μ̂)² > ∑ᵢ kᵢ` holds (the residual sum of squares exceeds the sum of the fitted
Poisson variances), then the joint score equations have a solution `(â, b̂)` with `â > 0` and
`b̂ > 0`: the [shape score](../likelihood-equations-and-efficiency-of-the-gamma/shape-score.md)
`∂ℓ/∂a` and the [rate score](../likelihood-equations-and-efficiency-of-the-gamma/rate-score.md)
`∂ℓ/∂b` both vanish at `(â, b̂)`.

The condition is the positivity of the numerator `∑ᵢ ((kᵢ - sᵢ μ̂)² - kᵢ)` of the Dean–Lawless
(1989) score statistic for overdispersion. At a common size factor it is `M < V`
([the condition at a common size factor](overdispersed-const-iff.md)), and the solution is unique
([exactly one joint score root](exists-unique-score-root-const-varying.md)). At heterogeneous size
factors it need not be: at size factors `(1000, 1/100, 100)` and counts `(12, 1, 6)`, which satisfy
the condition, the joint score equations have two solutions in `(0, ∞)²` with different shapes
([two sign changes give two roots](exists-two-score-roots.md)).
