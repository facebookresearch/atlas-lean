# Position history of the normalized burn

For a real time `t`, the position of the vehicle in the normalized burn, measured along the thrust
direction from the origin, is `x(t) = t + (2 - t) log ((2 - t) / 2)`, with `x(0) = 0`. The
intended domain is the burn interval `[0, 1]`; the formula is the usual one for every `t < 2`,
where the [mass](burn-mass.md) `2 - t` is positive. With the conventions `log 0 = 0` and
`log u = log |u|`, it is `2` at the depletion time `t = 2` (also the limit from below) and
`t + (2 - t) log ((t - 2) / 2)` for `t > 2`.
