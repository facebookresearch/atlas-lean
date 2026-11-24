# Rotor Port

A lumped (meanline) port of a rotor control volume: the flow state at one representative
point of azimuth `φ`, radius `r` and axial station `z`, with the port area `A`. No port surface is
modelled, and `r` is the port's effective moment radius (see `axialMomentFlux`). In the local
cylindrical frame at the representative point the inertial fluid velocity has the components
`(cr, cθ, cz)`, so `cθ` is the inertial swirl velocity, positive along `e_θ`, and the outward
unit normal has the meridional components `(nr, 0, nz)`, `nr ^ 2 + nz ^ 2 = 1`. The density `ρ`,
the area `A` and the radius `r` are nonnegative.
