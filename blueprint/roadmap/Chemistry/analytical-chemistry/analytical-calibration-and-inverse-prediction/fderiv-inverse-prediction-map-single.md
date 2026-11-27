# Sensitivity coefficients of inverse prediction

The sensitivity coefficients of inverse prediction: for `b ≠ 0`, the partial derivative of the
[three-input inverse prediction](inverse-prediction-map.md) `f(y₀, a, b) = (y₀ - a) / b` at
`(y₀, a, b)` along the `i`-th input, its derivative applied to the `i`-th unit vector, is the
`i`-th entry of the gradient `g = (1 / b, -1 / b, -(y₀ - a) / b ^ 2)`.
