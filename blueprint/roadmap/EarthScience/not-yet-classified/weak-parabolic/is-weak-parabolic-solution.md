# Weak parabolic solutions

These are the weak solutions of `∂ₜu = ∂ₓ(κ ∂ₓu) + F` on
`(t0, t1) × (0, 1)` with zero boundary values that are continuous in time with values in
`L²(0,1)`.

`u` is the solution and `ux` its spatial derivative, both as functions of `(t, x)`. This is
the class `L²(t0, t1; H¹₀(0,1)) ∩ C([t0, t1]; L²(0,1))` of the standard theory (Evans,
§5.9.2 and §7.1.1). In space no representative is prescribed: at almost every time `u t` need
only agree almost everywhere on `[0, 1]` with an `H¹₀(0,1)` function (`WeakH10`) whose weak
derivative agrees almost everywhere on `[0, 1]` with `ux t`; the other conditions on a time
slice depend on it only up to such agreement, and those on the rectangle only up to equality
almost everywhere there. In time the given `u` is the representative: every time slice is in
`L²(0,1)` and the slices vary continuously in `L²(0,1)`, while the `H¹₀(0,1)` condition, which
imposes the boundary values, is required at almost every time only. In particular no profile
is required at the initial time, so the initial value may be any function of `L²(0,1)`.

Both sides of the weak equation are Lebesgue integrals, not Lean's default value `0` for a
non-integrable function: the class requires the forcing to be integrable against every test
function, and the left side is integrable for every test function once `κ` is a.e. bounded
and a.e. strongly measurable (`weak_parabolic_integrand_integrable`), as in
`weak_parabolic_unique`.
