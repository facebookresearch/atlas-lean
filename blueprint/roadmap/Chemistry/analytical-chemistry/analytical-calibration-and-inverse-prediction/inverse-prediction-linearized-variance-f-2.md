# First-order uncertainty of inverse prediction, uncorrelated inputs

For a nonzero slope `b`, let the inputs `(y₀, a, b)` be pairwise uncorrelated random variables
`X 0`, `X 1`, `X 2` with finite second moments on a probability space, with standard
uncertainties `u 0`, `u 1`, `u 2` (`Var[X i] = u i ^ 2`). The first-order linearization
`ω ↦ f(y₀, a, b) + f'(X ω - (y₀, a, b))` of the
[three-input inverse prediction](inverse-prediction-map.md) `f` at `(y₀, a, b)`, with `f'` its
Fréchet derivative there, has variance
`(u 0 ^ 2 + u 1 ^ 2) / b ^ 2 + (y₀ - a) ^ 2 / b ^ 4 * u 2 ^ 2`, including the
response-uncertainty term `u(y₀) ^ 2 / b ^ 2`. This is the
[first-order law of propagation for uncorrelated inputs](../../../Physics/quantities-and-measurement/propagation-of-measurement-uncertainty/measurement-function-linearized-variance-3.md)
with the [sensitivity coefficients of inverse prediction](fderiv-inverse-prediction-map-single.md).
