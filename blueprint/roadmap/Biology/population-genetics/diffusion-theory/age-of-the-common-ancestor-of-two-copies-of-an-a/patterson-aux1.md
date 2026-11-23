# Patterson Aux1

Patterson's first Appendix solution `a₁` (Equation A3):
`a₁(x) = 2 - x + 2 (1 - x) log (1 - x) / x`. It solves `generator 0 w x = w x / x` on
`(0, 1)` (`pattersonAux1_ode`; this is his Equation A2, `x² (1 - x) / 2 * w'' = w`,
divided by `x`), tends to `0` at `x = 0` and equals `1` at `x = 1` (Equations A5,
A6). At `x = 0` the Lean value is the totalized `2`, not the limit.
