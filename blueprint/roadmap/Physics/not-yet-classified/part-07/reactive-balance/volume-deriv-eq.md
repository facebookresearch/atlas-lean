# Volume derivative from the mass balance

If `rho` and `V` have
derivatives `rho'` and `V'` at the instant `t`, `rho t ≠ 0`, and the mass
`rho * V` has derivative `rho_in * Qin - rho t * Qout` at `t` (inflow of
density `rho_in`, outflow at the vessel density), then
`V' = (rho_in / rho t) * Qin - Qout - V t * rho' / rho t`. This shows why mass
conservation alone is insufficient for a volume law when the density
changes.
