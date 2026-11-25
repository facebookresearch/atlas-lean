# Gradient of inverse prediction

The gradient of inverse prediction with respect to `(y₀, a, b)`: the vector of partial
derivatives `(1 / b, -1 / b, -(y₀ - a) / b ^ 2)`. For `b ≠ 0` its entries are
[the derivatives of the one-variable slices](has-deriv-at-inverse-prediction-gradient.md) and the
coefficients of
[the Fréchet derivative of the three-input map](has-fderiv-at-inverse-prediction-map.md). At
`b = 0` inverse prediction is undefined, and for `y₀ ≠ a` its slice in the slope `b` has no
derivative there; all three entries are then `0`, by the convention `x / 0 = 0`, which is not a
gradient. The vector is the list
of sensitivity coefficients, not a gradient in an inner-product space.
