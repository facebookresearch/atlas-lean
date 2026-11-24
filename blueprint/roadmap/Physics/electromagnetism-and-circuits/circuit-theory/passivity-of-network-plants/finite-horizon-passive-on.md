# Finite-horizon passivity of a trajectory on an interval

For a [network plant](network-plant.md), a [trajectory](network-trajectory.md) and reals `a` and
`b`, the trajectory is finite-horizon passive on `[a, b]` when `E(b) - E(a) ≤ ∫_a^b s(t) dt`, where
`E` is the [storage](plant-storage.md) and `s` the [supply rate](plant-supply-rate.md).
