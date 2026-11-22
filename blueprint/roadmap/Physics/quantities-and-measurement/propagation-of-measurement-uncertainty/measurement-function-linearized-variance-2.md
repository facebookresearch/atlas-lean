# First-order law of propagation for a C¹ measurement function

If `f` is of class `C¹`
on an open set `U` containing the input estimate `x` (for instance an open set containing a box
around `x`), then `fderiv ℝ f x` is the derivative of `f` at `x` and the first-order law
`measurementFunction_linearizedVariance_firstOrder` holds for the linearization
`ω ↦ f x + fderiv ℝ f x (X ω - x)`.
