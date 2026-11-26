# Right-hand side of the gradually-varied-flow equation

For a rectangular channel of width `b`, Manning roughness `n`, bed slope `S0`, total discharge
`Q`, gravitational acceleration `g` and depth `y` (real numbers), the steady gradually-varied-flow
equation with energy coefficient `α = 1` declares the depth slope
`dy/dx = (S0 - S_f(y)) / (1 - (Q / b) ^ 2 / (g * y ^ 3))`, with `S_f` the
[friction slope](friction-slope.md). Its physical domain is `b, n, S0, g, y > 0` with `y` different
from the critical depth `yc = ((Q / b) ^ 2 / g) ^ (1 / 3)`. The expression is defined for all real
inputs, with the convention `a / 0 = 0`: on `b, g, y > 0` the denominator vanishes exactly at
`y = yc`, where the value is `0`, which is not a physical slope; and the term
`(Q / b) ^ 2 / (g * y ^ 3)` is `0` when `b = 0`, `g = 0` or `y = 0`. Inside `S_f`, a negative
hydraulic radius `R = (b * y) / (b + 2 * y)` enters as `R ^ (2 / 3) = -|R| ^ (2 / 3) / 2`, by the
convention `a ^ r = |a| ^ r * cos (π r)` for `a < 0`.
