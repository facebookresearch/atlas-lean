# First-order uncertainty of inverse prediction

For a nonzero slope `b`, let the inputs `(y₀, a, b)` be random variables `X 0`, `X 1`, `X 2`
with finite second moments on a probability space, with estimate `(y₀, a, b)`. The first-order
linearization `ω ↦ f(y₀, a, b) + f'(X ω - (y₀, a, b))` of the
[three-input inverse prediction](inverse-prediction-map.md) `f` at the estimate, built from its
[Fréchet derivative](has-fderiv-at-inverse-prediction-map.md) `f'`, has variance
`∑ i, ∑ j, gᵢ * gⱼ * cov[X i, X j]`, where `g = (1 / b, -1 / b, -(y₀ - a) / b ^ 2)`. This is the
[first-order law of propagation of uncertainty](../../../Physics/quantities-and-measurement/propagation-of-measurement-uncertainty/measurement-function-linearized-variance.md)
applied to inverse prediction. It is a GUM-style linearization: exact for the linearization, not
for the nonlinear map `(y₀, a, b) ↦ x₀`.
