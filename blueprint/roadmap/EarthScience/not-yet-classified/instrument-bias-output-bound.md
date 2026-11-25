# Instrument Bias Bound

Bounded instrument bias gives a deterministic output bound: with
`y = a * x + b + ε`, `a ≠ 0`, and `|ε| ≤ B`, the calibrated estimator
`(y - b) / a` differs from `x` by at most `B / |a|`.
