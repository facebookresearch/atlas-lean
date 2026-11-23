# Inlet-minus-outlet balance of the normalized saturations

For all real arguments, the interior fluxes cancel: the sum of the normalized saturations
`s 0, …, s n` changes under the [upwind step](upwind-step.md) by `ν * (f(s_in) - f(s n))`, where
`s_in` is the inflow state, `s n` the outlet cell and `f` the [fractional flow](frac-flow.md).
