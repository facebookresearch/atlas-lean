# Exit time of a vehicle from a traffic link

For an initial count `N0 ≥ 0` (the vehicles on the link at time `0`), cumulative arrival and
departure counts `A, D : [0, ∞) → [0, ∞)` counted from time `0` and an entry time `t ≥ 0`, the exit
time of the vehicle that enters at `t`, under first-in first-out order, is
`τ(t) = inf {s ≥ t : D(s) ≥ N0 + A(t)}` when that set is nonempty and `τ(t) = ∞` otherwise: the
first time at or after entry at which the departure count reaches the vehicle's number `N0 + A(t)`.
It takes values in `[0, ∞]`. For a right-continuous `D` the infimum is attained.
