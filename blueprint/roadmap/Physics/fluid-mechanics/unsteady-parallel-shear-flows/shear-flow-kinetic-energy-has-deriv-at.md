# Kinetic energy balance of a shear flow with wall work

Let `ρ > 0` and `L ≥ 0`, let `μ`, `λ` be real and `p(t)` a pressure, and let `U` be jointly twice
continuously differentiable in `(t, y)` such that the [parallel shear flow](shear-flow.md) of
constant density `ρ` with velocity `(U(t, y), 0, 0)`, `y` the wall-normal coordinate satisfies the
Navier–Stokes equations in conservative form (continuity, Cauchy momentum balance, and the Newtonian
stress with the uniform pressure `p(t)`, the shear viscosity `μ` and the second viscosity `λ`). Then
at every time `t`, the [kinetic energy per unit wall area](shear-kinetic-energy.md)
`K(t) = ∫_0^L ρ U(t, y)² / 2 dy` has the derivative
`K'(t) = -μ ∫_0^L U_y(t, y)² dy + μ (U U_y)(t, L) - μ (U U_y)(t, 0)`. The first term is the viscous
dissipation, nonpositive for `μ ≥ 0`; the boundary terms are the wall velocity times the wall shear
stress `μ U_y` at each wall.
