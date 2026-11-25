# Pressure-gradient formula of a plane slider

For real numbers `μ`, `U`, `h₀`, `h_L`, `L` and `x`, with `h = h(x)` the
[film thickness](slider-film.md), the pressure-gradient formula is `6 μ U (h - h_m) / h³` with
`h_m = 2 h₀ h_L / (h₀ + h_L)`. For `h₀, h_L > 0`, `h₀ ≠ h_L` and `L > 0` it is the derivative within
`[0, L]` of the [closed-form pressure](slider-pressure.md), which with it
[solves the Reynolds model](slider-pressure-is-reynolds-solution.md). With the convention
`a / 0 = 0`, `h_m = 0` when `h₀ + h_L = 0` and the formula is `0` when `h = 0`.
