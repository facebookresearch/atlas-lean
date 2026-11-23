# The physical saturation step normalizes to the upwind step

For all real arguments, the [normalized saturations](norm-sat.md) of the
[physical step](sat-step.md) are the [normalized upwind step](upwind-step.md) of the normalized
saturations, with the normalized inflow state and the [CFL number](cfl-number.md)
`ν = Q * dt / (φ * A * dx * ΔS)`, `ΔS = 1 - Sor - Swc`.
