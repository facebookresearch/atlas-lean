# Closed-form pressure of a plane slider

For real numbers `μ`, `U`, `h₀`, `h_L`, `L` and `x`, with `h = h(x)` the
[film thickness](slider-film.md), the closed-form pressure is
`6 μ U L (h₀ - h) (h - h_L) / ((h₀² - h_L²) h²)`. With the convention `a / 0 = 0`, it is `0` when
`h₀² = h_L²` or `h = 0`; the intended domain is `0 < h₀`, `0 < h_L`, `h₀ ≠ h_L` and `L > 0`, where
it [solves the Reynolds model](slider-pressure-is-reynolds-solution.md) with the
[pressure-gradient formula](slider-pressure-gradient.md).
