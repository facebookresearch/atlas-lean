# The upwind step keeps normalized saturations in the unit interval

For viscosities `μo > 0` and `μw > 0` and a CFL number `ν` with `0 ≤ ν * B ≤ 1`, where
`B = (μo + μw) ^ 2 / (2 * μo * μw)`, if the inflow state and every cell lie in `[0, 1]`, then
every cell of the [upwind step](upwind-step.md) lies in `[0, 1]`.
