# Weak solutions

**Weak solutions** of `∂ₜu = ∂ₓ(κ ∂ₓu) + F` on `(t0, t1) × (0, 1)` with zero boundary
values that are continuous in time with values in `L²(0,1)`.

`u` is the solution and `ux` its spatial derivative, both as functions of `(t, x)`. This is
the class `L²(t0, t1; H¹₀(0,1)) ∩ C([t0, t1]; L²(0,1))` of the standard theory (Evans,
§5.9.2 and §7.1.1), written with representatives: every time slice is in `L²(0,1)` and
the slices vary continuously in `L²(0,1)`, while the boundary values are imposed through
`H¹₀(0,1)` profiles at almost every time only. In particular no profile is required at the
initial time, so the initial value may be any function of `L²(0,1)`.

Both sides of the weak equation are Lebesgue integrals, not Lean's default value `0` for a
non-integrable function: the class requires the forcing to be integrable against every test
function, and the left side is integrable for every test function once `κ` is a.e. bounded
and a.e. strongly measurable (`weak_parabolic_integrand_integrable`), as in
`weak_parabolic_unique`.
