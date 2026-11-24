# Componentwise Jacobian remainder bound, unit-step form

If `f` is differentiable at
`x` and the one-variable segment function `φᵢ t = f i (x + t • δ)` of the selected component
`i` is `C²` with `|φᵢ'' t| ≤ H i` on `[0, 1]`, then `|jacobianRemainder f x δ i| ≤ H i / 2`;
the other components need no smoothness. This is the scalar bound applied to `φᵢ`
with unit step; the `fderiv`/`φᵢ'` identification uses the chain rule along the
segment. The second derivative of `φᵢ` already carries two factors of `δ`, so `H i` bounds
it along this one segment and is not a Hessian bound; see
`jacobianRemainder_component_le_of_scaled` for the `‖δ‖ ^ 2`-scaled form and
`jacobianRemainder_component_le_of_hessian` for the bound from a Hessian bound.
