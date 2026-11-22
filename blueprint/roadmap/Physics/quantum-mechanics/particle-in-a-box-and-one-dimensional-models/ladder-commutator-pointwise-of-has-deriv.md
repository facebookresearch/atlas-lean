# Pointwise ladder commutator for twice-differentiable functions

Pointwise ladder identity `annFun (creFun f) x - creFun (annFun f) x = f x`, for any `f`
with first and second derivatives at `x`: a formal identity of the differential expressions
(by `deriv` arithmetic plus the product rule; Mathlib `HasDerivAt.mul`,
`HasDerivAt.add/sub/div_const`).
