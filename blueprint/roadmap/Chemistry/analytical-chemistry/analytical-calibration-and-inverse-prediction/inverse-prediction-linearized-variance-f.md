# First-order uncertainty of inverse prediction

**First-order uncertainty of inverse prediction** (CH24.4). For a nonzero slope `b`, let the
inputs `(y₀, a, b)` be random variables `X 0`, `X 1`, `X 2` with finite second moments on a
probability space, with estimate `![y₀, a, b]`. The first-order linearization of
`inversePredictionMap` at the estimate, built from its Fréchet derivative, has variance
`∑ i, ∑ j, gᵢ * gⱼ * cov[X i, X j]`, where `g = inversePredictionGradient a b y₀`. This is
`Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder` applied to
`hasFDerivAt_inversePredictionMap`. It is a GUM-style (CHEM-S6) linearization: exact for the
linearization, never for the nonlinear map `(y₀, a, b) ↦ x₀`.
