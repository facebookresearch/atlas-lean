# Orbital equivalence, Lotka–Volterra to replicator

**Orbital equivalence, Lotka–Volterra to replicator** (Hofbauer–Sigmund 1998,
§7.5). Let `y` be a positive solution on `[0, ∞)` of the Lotka–Volterra equation with
`r = lvGrowth A`, `B = lvInteraction A` (every `r`, `B` arises this way, from `lvGame r B`).
The explicit time change `t = repTimeChange y`, `t(τ) = ∫₀^τ (1 + ∑ y_j)`, is `C¹` with
derivative `≥ 1` (orientation preserving) and `t(0) = 0`; the curve `repTrajectory y` solves
the replicator equation of the game `A` for all `t ≥ 0`, stays in the interior of the simplex,
and equals `ofLV (y τ)` at time `t(τ)`. The original times are **not** identified:
`τ < t(τ)` for `τ > 0` whenever there is at least one species. Boundary states are
excluded. Only Lotka–Volterra solutions existing for all `τ ≥ 0` are covered; solutions that
blow up in finite time (such as those produced by `replicator_orbitEquiv_lotkaVolterra` when
`∫₀^∞ x_none < ∞`) are not.
