# Friction slope of a rectangular channel from Manning's law

For a rectangular channel of width `b` carrying the total discharge `Q` at depth `y` under Manning
roughness `n` (real numbers), the friction slope is Manning's law solved for the slope:
`S_f(y) = (n * Q / (A * R ^ (2 / 3))) ^ 2` (real power), with flow area `A = b * y` and hydraulic
radius `R = (b * y) / (b + 2 * y)`. It is physical for `n > 0`, `b > 0`, `y > 0` and `Q ≥ 0`. It
is defined for all real inputs, with the conventions `a / 0 = 0`, `0 ^ r = 0` for `r ≠ 0` and
`a ^ r = |a| ^ r * cos (π r)` for `a < 0`: it is `0` when `b * y = 0` or `b + 2 * y = 0`, and a
negative hydraulic radius enters as `R ^ (2 / 3) = -|R| ^ (2 / 3) / 2`.
