# Weibull Survival

The Weibull survival function with shape `k` and scale `lam`: `1` for `x < 0` and
`exp (-(x / lam) ^ k)` for `0 ≤ x`, intended for `0 < k` and `0 < lam`. Its cumulative hazard
`(x / lam) ^ k` (`neg_log_weibullSurvival`) is the power-law form. For `0 < k` and `0 < lam` it is
the survival function `x ↦ P(X > x)` of ATLAS's Weibull law `ProbabilityTheory.weibullMeasure k lam`
(`weibullSurvival_eq_weibullMeasure_real_Ioi`).
