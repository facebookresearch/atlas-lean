# A vehicle exits in finite time iff the departures reach its number

For an initial count `N0 ≥ 0` and cumulative arrival and departure counts `A, D : [0, ∞) → [0, ∞)`,
let `τ(t)` be the [exit time](link-exit-time.md) of the vehicle that enters at time `t`. If `D` is
nondecreasing, then `τ(t) < ∞` if and only if `D(s) ≥ N0 + A(t)` for some time `s ≥ 0`. Otherwise
the vehicle never leaves, and its exit time is `∞`.
