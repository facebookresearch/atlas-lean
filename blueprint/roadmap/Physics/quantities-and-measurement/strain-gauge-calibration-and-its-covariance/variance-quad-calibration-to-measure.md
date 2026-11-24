# Variance quad Calibration to Measure

Bridge to measure-theoretic variance: for a probability mass function `q` on the scenarios,
`ProbabilityTheory.variance_add` splits Mathlib's variance of the output under `q.toMeasure`
into the variance of the first-order part, twice the cross covariance and the variance of the
remainder.
