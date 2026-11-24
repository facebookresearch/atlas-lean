# At a finite exit time the departure count equals the vehicle number

For an initial count `N0 ≥ 0` and cumulative arrival and departure counts `A, D : [0, ∞) → [0, ∞)`,
let `τ(t)` be the [exit time](link-exit-time.md) of the vehicle that enters at time `t`. If `D` is
continuous, `D(t) ≤ N0 + A(t)` (nonnegative storage on the link at entry), and the exit time is
finite, `τ(t) = e`, then `D(e) = N0 + A(t)`. For a strictly increasing `D` this makes `e` the only
time with that count; on a plateau `e` is the first time at or after `t` with that count, not an
arbitrary root.
