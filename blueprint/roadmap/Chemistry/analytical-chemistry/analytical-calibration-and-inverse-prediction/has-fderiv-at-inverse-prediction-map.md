# Fréchet derivative of inverse prediction

For a nonzero slope `b`, the [three-input map](inverse-prediction-map.md)
`f(y₀, a, b) = (y₀ - a) / b` has Fréchet derivative `h ↦ ∑ i, gᵢ * h i` at the input estimate
`(y₀, a, b)`, where `g = (1 / b, -1 / b, -(y₀ - a) / b ^ 2)`. This is the multivariate
statement; [the partial derivatives](has-deriv-at-inverse-prediction-gradient.md) are the
derivatives of its one-variable slices. At `b = 0` inverse prediction is undefined and the map
is not differentiable.
