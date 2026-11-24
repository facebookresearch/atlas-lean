# Exit time as entry time plus network-calculus delay

For an initial count `N0 ≥ 0` and cumulative arrival and departure counts `A, D : [0, ∞) → [0, ∞)`,
let `τ(t)` be the [exit time](link-exit-time.md) of the vehicle that enters at time `t`. For every
`N0`, `A`, `D` and `t`, in `[0, ∞]`, `τ(t) = t + d(t)`, where
`d(t) = inf {δ ≥ 0 : N0 + A(t) ≤ D(t + δ)}` (`∞` for an empty set) is the network-calculus virtual
delay of the offset arrival count `s ↦ N0 + A(s)` against the departure count `D`. Both sides are
`∞` exactly when the departure count never reaches `N0 + A(t)` at or after `t`.
