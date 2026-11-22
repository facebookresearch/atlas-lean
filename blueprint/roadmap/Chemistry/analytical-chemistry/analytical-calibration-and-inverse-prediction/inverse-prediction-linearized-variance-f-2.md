# First-order uncertainty of inverse prediction, uncorrelated inputs

**First-order uncertainty of inverse prediction, uncorrelated inputs** (CH24.4). For a
nonzero slope `b` and random inputs `X 0`, `X 1`, `X 2` for `(y₀, a, b)` that are pairwise
uncorrelated, with standard uncertainties `u 0`, `u 1`, `u 2` (`Var[X i] = u i ^ 2`), the
variance of the first-order linearization of `inversePredictionMap` at `(y₀, a, b)` is
`(u 0 ^ 2 + u 1 ^ 2) / b ^ 2 + (y₀ - a) ^ 2 / b ^ 4 * u 2 ^ 2`, including the
response-uncertainty term `u(y₀) ^ 2 / b ^ 2`. This is
`Chemistry.Uncertainty.measurementFunction_linearizedVariance_firstOrder_uncorrelated` with the
sensitivity coefficients of `fderiv_inversePredictionMap_single`.
