# The physical saturation step normalizes to the upwind step

For all real arguments, the [normalized saturations](norm-sat.md) of the
[physical step](sat-step.md) are the [normalized upwind step](upwind-step.md) of the normalized
saturations, with the normalized inflow state and the [CFL number](cfl-number.md)
`ν = Q * dt / (φ * A * dx * ΔS)`, `ΔS = 1 - Sor - Swc`. The statement covers the degenerate inputs,
with the convention `x / 0 = 0`: when `ΔS = 0`, every normalized saturation and `ν` are `0`, so both
sides are `0`; when `φ * A * dx = 0`, the physical step leaves the saturations unchanged and
`ν = 0`, so both sides are the normalized saturation of `S i`; and the fractional flow is `0` where
its denominator vanishes.
