# Cosine coefficient of a cable profile

For a real number `L`, a function `V : ℝ → ℝ → ℝ` of time and position, a natural number `n` and a
real time `t`, the `n`-th cosine coefficient of the profile `V(t, ·)` is

`c_n(t) = ∫₀ᴸ V(t, x) cos (n π x / L) dx`,

the integral of the profile against the `n`-th [mode](cos-mode.md). It is unnormalized: for an
absolutely convergent cosine series `∑_m b_m cos (m π x / L)` the coefficient is `b_0 L` for
`n = 0` and `b_n L / 2` for `n ≥ 1` ([coefficients](integral-cable-series-mul-cos-mode.md), at
`t = 0`). The integral is oriented, so for `L < 0` it is minus the integral over `[L, 0]`, and
with the convention that a function not integrable on the interval has integral `0`,
`c_n(t) = 0` when `x ↦ V(t, x) cos (n π x / L)` is not integrable there.
