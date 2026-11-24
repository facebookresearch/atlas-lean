# Exit by a given time for right-continuous departures

For an initial count `N0 ≥ 0` and cumulative arrival and departure counts `A, D : [0, ∞) → [0, ∞)`,
let `τ(t)` be the [exit time](link-exit-time.md) of the vehicle that enters at time `t`. If `D` is
nondecreasing and right-continuous, then for all times `s ≥ t`, `τ(t) ≤ s` if and only if
`N0 + A(t) ≤ D(s)`. So the exit time is the least `s ≥ t` with `N0 + A(t) ≤ D(s)`, and on a
departure plateau at the vehicle's number it is the left end of the plateau, or `t` when the plateau
begins before `t`. Right-continuity makes
the least time attained; at a jump of a left-continuous count the equivalence fails.
