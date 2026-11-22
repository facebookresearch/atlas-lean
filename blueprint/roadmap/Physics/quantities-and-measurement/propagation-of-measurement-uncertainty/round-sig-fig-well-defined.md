# Rounding to significant figures is well defined

`roundSigFig k` is a total function
`ℝ → ℝ`, with ties broken by `round`. For `x ≠ 0` and a positive count `k : ℕ+` the textbook
description determines it: there is exactly one decimal exponent `m`, the place `10 ^ m` of the
leading significant digit, with `10 ^ m ≤ |x| < 10 ^ (m + 1)`, and `roundSigFig k x` rounds `x`
at the place `10 ^ (m + 1 - k)` for that `m`.
