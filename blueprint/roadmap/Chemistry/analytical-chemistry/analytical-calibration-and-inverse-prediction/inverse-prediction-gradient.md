# Gradient of inverse prediction

The gradient of inverse prediction with respect to `(y₀, a, b)`: the partial
derivatives `1 / b`, `-1 / b` and `-(y₀ - a) / b ^ 2`. For `b ≠ 0` they are the derivatives of
the one-variable slices (`hasDerivAt_inversePredictionGradient`) and the coefficients of the
Fréchet derivative of the three-input map (`hasFDerivAt_inversePredictionMap`). At `b = 0`
inverse prediction is undefined and the slope derivative does not exist; Lean's totalized
division makes all three entries `0` there, which is not a gradient, so every lemma that treats
this vector as the gradient requires `b ≠ 0`. This is an explicit `3`-vector of sensitivity
coefficients, not Mathlib's inner-product-space gradient, whose Hilbert-space setup the
first-order law does not need.
