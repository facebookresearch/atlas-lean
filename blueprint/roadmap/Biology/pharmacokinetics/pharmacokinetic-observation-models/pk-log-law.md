# Log-linear form of a bolus concentration with multiplicative error

For `D > 0` and `V > 0` and all real `k`, sampling times `t j` and errors `ε j` (`j` among `n`
observations), the concentration observation `Y j = (D / V) * exp (-k * t j) * exp (ε j)`, the bolus
concentration times a log-additive error factor, has logarithm
`log (Y j) = 1 * log (D / V) + (-t j) * k + ε j`: a linear model with design row `(1, -t j)` and
coefficient vector `(log (D / V), k)`. This is an exact identity for every value of the errors: a
multiplicative error is additive on the log scale, while an additive concentration error would not
be an additive log error.
