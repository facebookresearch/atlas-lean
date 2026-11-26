# Upper bound on a² times the shape score at a rate score root

Let `a > 0`, let `s₁, …, sₙ` be positive size factors and `k₁, …, kₙ` counts, and let `b > 0` solve
the [rate score](../likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) equation
`∑ᵢ (a / b - (a + kᵢ) / (b + sᵢ)) = 0`. With the fitted means `mᵢ = sᵢ a / b`, the
[shape score](../likelihood-equations-and-efficiency-of-the-gamma/shape-score.md) of the
[log marginal likelihood](../likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
`ℓ` satisfies `a² ∂ℓ/∂a (a, b) ≤ ∑ᵢ ((kᵢ - (kᵢ - mᵢ)²) / 2 + (mᵢ - kᵢ) mᵢ² / (a + mᵢ) + kᵢ³ / a)`.

Along the [rate root](rate-root.md) `b = b̂(a)`, for `n ≥ 1` and some positive count, `a / b̂(a)`
tends to the [pooled Poisson rate](pooled-mean.md) `μ̂` as `a → ∞`
([the Poisson limit](tendsto-div-rate-root.md)), so the bound tends to
`(∑ᵢ kᵢ - ∑ᵢ (kᵢ - sᵢ μ̂)²) / 2`. This limit is negative under the overdispersion condition
`∑ᵢ (kᵢ - sᵢ μ̂)² > ∑ᵢ kᵢ`.
