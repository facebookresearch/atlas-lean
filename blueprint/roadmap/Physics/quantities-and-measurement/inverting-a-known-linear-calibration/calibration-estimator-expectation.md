# Calibration estimator expectation

Unbiasedness of the calibrated estimator: with known calibration
`y = a * x + b + ε`, `a ≠ 0`, integrable error `ε` whose expectation is
`e`, the expectation of the estimator `(y - b) / a` is `x + e / a`.
In particular when `E[ε] = 0` it is exactly `x`. A fitted `a` creates
a different nonlinear bias problem and is out of scope.
