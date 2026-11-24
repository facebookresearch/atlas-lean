# Exponential decay to rest

For `ε > 0` and an equilibrium `(vr, wr)`: if
`restFactor vr (v s - vr) ≤ -c` along a solution for `s ∈ [0, t]`, then
`restEnergy(t) ≤ e^{-2 min c (b ε) t} restEnergy(0)`.

Proof: `restFlux_le` and Mathlib's Grönwall bound `le_gronwallBound_of_liminf_deriv_right_le`.
