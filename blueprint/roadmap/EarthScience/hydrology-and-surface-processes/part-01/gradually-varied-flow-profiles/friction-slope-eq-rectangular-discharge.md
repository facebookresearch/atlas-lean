# Friction slope as the bed slope scaled by a squared discharge ratio

For a bed slope `S0 > 0` and all real `n`, `b`, `Q` and `y`, the friction slope
`S_f(y) = (n * Q / ((b * y) * ((b * y) / (b + 2 * y)) ^ (2 / 3))) ^ 2` equals
`S0 * (Q / Q_N(y)) ^ 2`, where `Q_N(y) = (√S0 / n) * (b * y) * ((b * y) / (b + 2 * y)) ^ (2 / 3)`
is the rectangular-channel Manning discharge at bed slope `S0`, the uniform-flow discharge at
depth `y`. The identity also holds where a denominator vanishes, both sides then being read with
the convention `x / 0 = 0` (for instance both are `0` when `n = 0`), and for a negative hydraulic
radius `R = (b * y) / (b + 2 * y)`, which enters both sides as `R ^ (2 / 3) = -|R| ^ (2 / 3) / 2` by
the convention `x ^ r = |x| ^ r * cos (π r)` for `x < 0`.
