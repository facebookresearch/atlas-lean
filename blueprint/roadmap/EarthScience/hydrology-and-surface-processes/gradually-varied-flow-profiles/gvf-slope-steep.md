# Signs of the gradually-varied-flow slope on a steep channel

Let `b > 0` be the channel width, `n > 0` the Manning roughness, `S0 > 0` the bed slope and
`g > 0` the gravitational acceleration, and let `yn > 0` be a normal depth for the discharge `Q`:
`(√S0 / n) * (b * yn) * ((b * yn) / (b + 2 * yn)) ^ (2 / 3) = Q`. Let
`yc = ((Q / b) ^ 2 / g) ^ (1 / 3)` be the critical depth and
`G(y) = (S0 - S_f(y)) / (1 - (Q / b) ^ 2 / (g * y ^ 3))` the right-hand side of the
gradually-varied-flow equation, with `S_f` the
[friction slope](friction-slope.md).

If the channel is steep, `yn < yc`, then `G(y) > 0` for `y > yc` (zone 1), `G(y) < 0` for
`yn < y < yc` (zone 2) and `G(y) > 0` for `0 < y < yn` (zone 3). Read as `dy/dx` with `x`
positive downstream, the depth rises downstream in zones 1 and 3 and falls in zone 2.
