# Partition function of the selection–mutation stationary density

For real numbers `α`, `θ₁` and `θ₂`, let

`Z(α, θ₁, θ₂) = ∫₀¹ m(x) dx`, with `m(x) = 2 e^(2αx) x ^ (θ₁ - 1) (1 - x) ^ (θ₂ - 1)`

the [selection–mutation speed density](../scale-and-speed-of-one-dimensional-diffusions/selection-mutation-speed-density.md), where the integral of a function that is not integrable on `[0, 1]` is taken to be
`0`. For `θ₁, θ₂ > 0`, `Z` is [finite](interval-integrable-selection-mutation-s.md) and
[positive](selection-mutation-partition-pos.md), and `m / Z` is the probability density on
`(0, 1)` of Wright's stationary distribution of the Wright–Fisher diffusion with genic selection
`α` and two-way mutation `θ₁`, `θ₂`. For `θ₁ ≤ 0` or `θ₂ ≤ 0`, `m` is not integrable near `0` or
near `1` and `Z = 0`.

## Sources

- S. Wright, *Evolution in Mendelian populations*, Genetics 16 (1931), 97–159.
