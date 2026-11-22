# Has Deriv At acoustic Mode Energy

Energy identity for the acoustic mode: if `A` and `B` are
differentiable in time with
`A' = -γ * pbar * (π / L) * B + (γ - 1) * H` and
`ρ * B' = (π / L) * A - r * B` (with `B'` the derivative value), then
the energy `E(t) = L * (A(t)^2 / (γ * pbar) + ρ * B(t)^2) / 4` has
derivative
`L * (γ - 1) * A(t) * H / (2 * γ * pbar) - r * L * B(t)^2 / 2`:
the heat-release source term minus the algebraic damping term
`r * L * B(t)^2 / 2` (a genuine dissipation under `0 ≤ r` and
`0 < L`; see `acousticModeEnergy_deriv_nonpos_of_no_heat`). Here `H` is a
constant heat-release amplitude for this identity.
