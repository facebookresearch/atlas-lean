# A bias bound B limits the estimator error to B over the modulus of a

Let the reading of an instrument follow the known linear calibration `y = a x + b + ε`, with slope
`a ≠ 0`, offset `b`, true value `x` and error `ε` (all real), and let the bias satisfy `|ε| ≤ B`.
Then the [calibrated estimator](calibration-estimator-error.md) is within `B / |a|` of the true
value: `|(a x + b + ε - b) / a - x| ≤ B / |a|`. The bound is deterministic: no probability is
involved.
