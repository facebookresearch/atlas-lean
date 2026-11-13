# Covariance

The covariance `E[(X - E X) * (Y - E Y)]` under the weight `p` (MF06.2). Mathlib's
`ProbabilityTheory.covariance` integrates against a measure and its algebra needs `MemLp`
hypotheses; this finite sum needs none (`covariance_toMeasure_eq` relates them).
