# Jacobian propagation is an APPROXIMATION

The first-order value of `f` at
`x + δ` is `f x + fderiv ℝ f x δ`; `jacobianRemainder f x δ` is the leftover
`f (x + δ) - f x - fderiv ℝ f x δ`, bounded by the lemmas below but NOT zero in
general: for the square map on `Fin 1 → ℝ` at `x = 0` and `δ = 1 / 2` it is `1 / 4`
(see the tests). Where `f` is not differentiable at `x`, Mathlib's `fderiv ℝ f x` is `0`
and the value is just `f (x + δ) - f x`; every bound below assumes differentiability at
`x`.
