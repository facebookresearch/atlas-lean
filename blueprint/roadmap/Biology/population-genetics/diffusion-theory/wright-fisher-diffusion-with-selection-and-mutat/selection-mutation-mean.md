# Stationary mean under selection–mutation balance

For real numbers `α`, `θ₁` and `θ₂`, let

`μ(α, θ₁, θ₂) = (∫₀¹ x m(x) dx) / Z(α, θ₁, θ₂)`,

where `m` is the
[selection–mutation speed density](../scale-and-speed-of-one-dimensional-diffusions/selection-mutation-speed-density.md)
and `Z = ∫₀¹ m(x) dx` its [partition function](selection-mutation-partition.md), the integral of a
function that is not integrable on `[0, 1]` is taken to be `0`, and division by `0` gives `0`. For
`θ₁ ≤ 0` or `θ₂ ≤ 0` the density `m` is not integrable on `[0, 1]`, so `Z = 0` and `μ = 0`. The
intended domain is `θ₁, θ₂ > 0`, where [`Z > 0`](selection-mutation-partition-pos.md) and `μ` is
the mean of the probability density `m / Z` on `(0, 1)`, the stationary mean allele frequency under
selection–mutation balance.
