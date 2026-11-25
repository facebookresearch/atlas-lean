# The gradually-varied-flow slope vanishes at the normal depth

Let `b > 0` be the channel width, `n > 0` the Manning roughness, `S0 > 0` the bed slope and
`g > 0` the gravitational acceleration, and let `yn > 0` be a normal depth for the discharge `Q`:
`(√S0 / n) * (b * yn) * ((b * yn) / (b + 2 * yn)) ^ (2 / 3) = Q`. Let
`yc = ((Q / b) ^ 2 / g) ^ (1 / 3)` be the critical depth and
`G(y) = (S0 - S_f(y)) / (1 - (Q / b) ^ 2 / (g * y ^ 3))` the right-hand side of the
gradually-varied-flow equation, with `S_f` the
[friction slope](friction-slope.md).

If `yn ≠ yc`, then `G(yn) = 0`: uniform flow at the normal depth is a constant-depth solution of
the equation. At `yn = yc` the quotient would be `0 / 0`, which the hypothesis `yn ≠ yc` keeps
out.
