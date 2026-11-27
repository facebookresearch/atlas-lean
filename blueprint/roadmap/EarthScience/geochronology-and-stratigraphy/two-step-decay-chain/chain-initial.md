# Chain parent and distinct-rate daughter start at P0 and D0

For all real `l1`, `l2`, `P0` and `D0`, the parent `P(t) = P0 * exp (-l1 * t)` starts at
`P(0) = P0`, and the distinct-rate daughter
`D(t) = D0 * exp (-l2 * t) + P0 * l1 / (l2 - l1) * (exp (-l1 * t) - exp (-l2 * t))` starts at
`D(0) = D0`, also for `l1 = l2` (where the formula is read with `x / 0 = 0`).
