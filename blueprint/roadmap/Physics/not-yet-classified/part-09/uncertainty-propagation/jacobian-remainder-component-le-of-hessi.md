# Componentwise remainder bound from a Hessian bound

Let `f` be differentiable at `x`,
let its component `i` be `C²` on an open set `U` containing the box `Set.Icc lo hi`, and let
the second Fréchet derivative of that component satisfy
`‖fderiv ℝ (fderiv ℝ (fun y => f y i)) y‖ ≤ H i` on the box, the operator norm for the sup
norm on `Fin n → ℝ`; the other components need no smoothness. For `x` and `x + δ` in the box,
`|jacobianRemainder f x δ i| ≤ H i / 2 * ‖δ‖ ^ 2`. This is
`Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le` for the component
`fun y => f y i`; the chain rule identifies its derivative at `x` with component `i` of
`fderiv ℝ f x`.
