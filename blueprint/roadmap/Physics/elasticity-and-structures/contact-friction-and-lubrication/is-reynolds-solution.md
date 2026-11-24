# Solutions of the Reynolds equation for a plane slider

For real numbers `μ` (viscosity), `U` (sliding speed), `h₀`, `h_L` and `L`, and functions `p` and
`p'`, the pair `(p, p')` solves the Reynolds model when, at every `x ∈ [0, L]`, `p` has derivative
`p'(x)` within `[0, L]` and `y ↦ h(y)³ p'(y)` has derivative `6 μ U (h_L - h₀) / L` within `[0, L]`
(one-sided at the ends), and `p(0) = p(L) = 0`. Here `h` is the [film thickness](slider-film.md).
This is the reduced model `(h³ p')' = 6 μ U h'` with ambient pressure at both ends and no
cavitation; it depends only on the values of `p` and `p'` on `[0, L]`. With the convention
`a / 0 = 0` the slope `(h_L - h₀) / L` is `0` when `L = 0`; the intended domain is `L > 0`, and for
`L < 0` the interval `[0, L]` is empty, so only `p(0) = p(L) = 0` remains.
