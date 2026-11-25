# Measure bound on the bad event of inverse prediction

Let `μ` be a measure on a measurable space `Ω`, not necessarily a probability measure, let `a`,
`E ≥ 0` and `p` be real numbers and `b ≠ 0`, and let `x` and `e` be real functions on `Ω`. If

`μ{ω : E < |e(ω)|} ≤ max(p, 0)`,

then the [inverse prediction](inverse-prediction.md) `x̂ = (y − a) / b` of the observation
`y(ω) = b x(ω) + a + e(ω)` satisfies

`μ{ω : E / |b| < |x̂(ω) − x(ω)|} ≤ max(p, 0)`.

The sets are not assumed measurable: `μ` is applied to them as an outer measure. The bad event of
the recovered input is contained in the bad event of the residual, by the
[bound with exact parameters](inverse-prediction-error-le-known-params.md); no distributional
assumption on the residual is made.
