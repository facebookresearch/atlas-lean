# Pore-volume identification

With known `rho0` and `cfl` and a
nonzero pressure excursion, produced mass determines the pore volume:
`Vp = ΔM / (rho0 * (1 - exp (cfl * (p - p0))))`.
