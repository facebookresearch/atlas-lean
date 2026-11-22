# Derivative of the logarithm of a power law

The gradient of the logarithm of a power law: `∂(log |y|)/∂xᵢ = p i / x i` when every
`x i ≠ 0`, where Mathlib's `Real.log y` is `log |y|` for `y < 0`. Equivalently
`∂y/∂xᵢ = y * (p i / x i)`.
