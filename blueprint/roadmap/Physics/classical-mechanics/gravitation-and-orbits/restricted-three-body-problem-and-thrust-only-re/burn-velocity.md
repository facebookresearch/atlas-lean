# Velocity history of the normalized burn

For a real time `t`, the velocity of the vehicle in the normalized burn, measured along the thrust
direction, is `v(t) = log (2 / (2 - t))`, from rest at `t = 0`. The intended domain is the burn
interval `[0, 1]`; the formula is the usual one for every `t < 2`, where the
[mass](burn-mass.md) `2 - t` is positive. With the conventions `u / 0 = 0`, `log 0 = 0` and
`log u = log |u|`, it is `0` at the depletion time `t = 2` and `log (2 / (t - 2))` for `t > 2`.
