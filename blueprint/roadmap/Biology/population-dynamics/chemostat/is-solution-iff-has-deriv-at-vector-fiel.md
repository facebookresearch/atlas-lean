# The single-species chemostat in the chemostat model's coordinates

`(S, x)` solves the
single-species chemostat (`IsSolution`) exactly when, at every time `t ≥ 0`, the curve
`t ↦ ![x t, S t]` in `Fin 2 → ℝ` (biomass first, then substrate) has the two-sided derivative
`vectorField (mmRate m a) D S⁰ y` of the chemostat model `Domains.Biology.Dynamics.Chemostat`,
whose Monod growth rate is `μ(S) = m S / (a + S)`.
