# Design Matrix

The design matrix of the simple linear model `y i = a + b * x i + e i`, with row `i` equal
to `(1, x i)` (MF06.3). It identifies `olsIntercept` and `olsSlope` with ATLAS's matrix
estimator (`olsEstimator_designMatrix`); Mathlib has no design-matrix constructor.
