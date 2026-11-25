# The upwind step in conservative finite-volume form

For all real arguments, the [upwind step](upwind-step.md) on cells `0, …, n` is the finite-volume
step of unit cell width and time step `ν` with the face fluxes `F 0 = f(s_in)` and
`F (j + 1) = f(s j)`: `s i - ν * (f(s i) - f(s (i - 1))) = s i + ν * (-(F (i + 1) - F i))`. Each
face carries the [fractional flow](frac-flow.md) of its left (upwind) state, the boundary face `0`
that of the inflow state. This includes viscosities and states for which the denominator of `f`
vanishes, where `f` is `0` by the convention `x / 0 = 0`.
