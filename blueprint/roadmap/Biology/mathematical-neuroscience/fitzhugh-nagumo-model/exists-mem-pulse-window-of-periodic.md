# Nonconstant periodic orbits pass through the window `restFactor > 0`

For `b, ε > 0` and
an equilibrium `(vr, wr)` with `vr² ≤ 4`, a `T`-periodic solution that is not the constant rest
state visits a state whose voltage displacement `v - vr` lies in the window
`pulseRootLow vr < v - vr < pulseRootHigh vr` where `restFactor vr > 0` (`restFactor_pos_iff`).
For `vr ≤ -1` the window consists of positive amplitudes (`pulseRootLow_nonneg`), the pulses
after which the voltage rises (`isRisingAfterPulse_iff`); for `-1 < vr < 2` it also contains
nonpositive displacements (`pulseRootLow_neg`), at which the voltage need not rise; at `vr = ±2`
it is empty, so no nonconstant periodic solution exists there.
