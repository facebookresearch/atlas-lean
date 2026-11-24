# Stationary variance under selection–mutation balance

For real numbers `α`, `θ₁` and `θ₂`, let

`v(α, θ₁, θ₂) = (∫₀¹ (x - μ)² m(x) dx) / Z(α, θ₁, θ₂)`,

where `m` is the
[selection–mutation speed density](../scale-and-speed-of-one-dimensional-diffusions/selection-mutation-speed-density.md),
`Z = ∫₀¹ m(x) dx` its [partition function](selection-mutation-partition.md) and
`μ = μ(α, θ₁, θ₂)` the [stationary mean](selection-mutation-mean.md), the integral of a function
that is not integrable on `[0, 1]` is taken to be `0`, and division by `0` gives `0`. For `θ₁ ≤ 0`
or `θ₂ ≤ 0` the density `m` is not integrable on `[0, 1]`, so `Z = 0` and `v = 0`. The intended
domain is `θ₁, θ₂ > 0`, where [`Z > 0`](selection-mutation-partition-pos.md) and `v` is the
variance of the probability density `m / Z` on `(0, 1)`.
