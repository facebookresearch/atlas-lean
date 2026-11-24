# For a ≠ 0, the calibrated value is x + ε / a, an error of ε / a

Let the reading of an instrument follow the known linear calibration `y = a x + b + ε`, with slope
`a ≠ 0`, offset `b`, true value `x` and error `ε` (all real). The calibrated estimator `(y - b) / a`
differs from the true value by exactly `ε / a`: `(a x + b + ε - b) / a - x = ε / a`.

The slope must be nonzero: for `a = 0` the left side is `-x` (by the convention `z / 0 = 0`) and the
right side is `0`.

Equivalently, the calibrated value is the true value plus the scaled error:
`(a x + b + ε - b) / a = x + ε / a`.
