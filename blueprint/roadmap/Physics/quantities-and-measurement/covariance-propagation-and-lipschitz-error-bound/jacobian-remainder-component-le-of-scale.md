# Componentwise remainder bound, `‖δ‖ ^ 2`-scaled segment form

If `f` is differentiable
at `x` and the segment function `φᵢ t = f i (x + t • δ)` of the selected component `i` is `C²`
with `|φᵢ'' t| ≤ H i * ‖δ‖ ^ 2` on `[0, 1]`, where `‖δ‖` is Mathlib's sup norm on
`Fin n → ℝ`, then `|jacobianRemainder f x δ i| ≤ H i / 2 * ‖δ‖ ^ 2`. This is
`jacobianRemainder_component_le` for the bound `H i * ‖δ‖ ^ 2`. The hypothesis still bounds
the second derivative along the given segment, not the Hessian of `f i`; for a Hessian
bound use `jacobianRemainder_component_le_of_hessian`. With the unscaled hypothesis
`|φᵢ'' t| ≤ H i`, the `‖δ‖ ^ 2` conclusion is false: the square map at `δ = 1 / 2` is a
counterexample (see the tests).
