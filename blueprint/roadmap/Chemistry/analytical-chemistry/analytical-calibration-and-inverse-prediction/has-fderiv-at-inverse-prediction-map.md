# Fréchet derivative of inverse prediction

**Fréchet derivative of inverse prediction** (CH24.4). For a nonzero slope `b`, the
three-input map `inversePredictionMap` has Fréchet derivative `h ↦ ∑ i, gᵢ * h i` at the input
estimate `(y₀, a, b)`, where `g = inversePredictionGradient a b y₀`. This is the multivariate
statement; `hasDerivAt_inversePredictionGradient` gives only the one-variable slices. At `b = 0`
inverse prediction is undefined and the map is not differentiable.
