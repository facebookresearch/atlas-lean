# Log Ratio

The logarithm `log (x / x0)` of the ratio of two positive quantities of the *same*
dimension `d`. Both arguments share the dimension index, so a ratio of quantities of
different dimensions is a type error; only after the type-level quotient `d / d = 1`
is formed is the coordinate ratio passed to `Real.log`.
