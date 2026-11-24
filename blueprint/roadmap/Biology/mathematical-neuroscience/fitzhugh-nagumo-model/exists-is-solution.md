# Global existence

For `b, ε > 0` every initial state `(v₀, w₀)` has a solution of the
FitzHugh–Nagumo system on `[0, ∞)`.

Proof: the maximal solution of `ode_maximal_solution_exit_compact` (`U = univ`, `t₀ = 0`) stays
over `[0, T] ∩ J` in the compact set `[0, T] ×ˢ {energy ≤ R}`, `R = max (energy₀) (trapRadius + 1)`
(`IsSolution.energy_le`, applied on `[0, T]`); if some `T ≥ 0` were not in its open interval
`J`, the time `max c 0` would contradict the forward exit from that compact set.
