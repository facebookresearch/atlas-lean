# Normalized upwind step on a chain with inflow

On a chain of `n + 1` cells with normalized saturations `s 0, …, s n` and an inflow state `s_in`
at the left boundary, one normalized upwind step with CFL number `ν` replaces `s i` by the
[local upwind update](upwind-update.md) `s i - ν * (f(s i) - f(s (i - 1)))`, where `f` is the
[fractional flow](frac-flow.md) and the upwind state of the first cell, `s (-1)`, is `s_in`. It is
defined for all real arguments, `f` being `0` where its denominator vanishes, by the convention
`x / 0 = 0`.
