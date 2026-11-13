# Empirical area under the ROC curve

Trapezoidal area under the empirical ROC curve of positive scores `x` and negative scores
`y`: the sum over the distinct observed scores `t` of the trapezoid from the point
`(rocRateAbove y t, rocRateAbove x t)` to `(rocRate y t, rocRate x t)`.
