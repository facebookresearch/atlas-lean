# First in, first out: a later entry exits no earlier

For an initial count `N0 ≥ 0` and cumulative arrival and departure counts `A, D : [0, ∞) → [0, ∞)`,
let `τ(t)` be the [exit time](link-exit-time.md) of the vehicle that enters at time `t`. If `A` is
nondecreasing, then `τ` is nondecreasing in `t` (in `[0, ∞]`), for every `N0` and every `D`: a
vehicle that enters later leaves no earlier, and an entry with no finite exit time is followed only
by entries with none.
