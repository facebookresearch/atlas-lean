# Sign of the depth gradient of a gradually varied profile

Let `b > 0` be the channel width, `n > 0` the Manning roughness, `S0 > 0` the bed slope and
`g > 0` the gravitational acceleration, and let `yn > 0` be a normal depth for the discharge `Q`:
`(√S0 / n) * (b * yn) * ((b * yn) / (b + 2 * yn)) ^ (2 / 3) = Q`. Let
`yc = ((Q / b) ^ 2 / g) ^ (1 / 3)` be the critical depth and
`G(y) = (S0 - S_f(y)) / (1 - (Q / b) ^ 2 / (g * y ^ 3))` the right-hand side of the
gradually-varied-flow equation, with `S_f` the
[friction slope](friction-slope.md).

If a depth profile `Y` (distance `x` positive downstream) satisfies the equation at one point
`x`, that is `Y` has derivative `G(Y(x))` at `x`, with `Y(x) > 0` and `Y(x) ≠ yc`, then the
derivative there has sign `sign (Y'(x)) = sign (Y(x) - yn) * sign (Y(x) - yc)`. No existence of
such a profile is claimed.
