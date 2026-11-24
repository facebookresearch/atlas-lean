# Rounding to significant figures is well defined

For `x ≠ 0` and a count `k ≥ 1`, the textbook description determines the rounding of `x` to `k`
significant figures: there is exactly one integer `m` such that both `10 ^ m ≤ |x| < 10 ^ (m + 1)`
and the rounded value is `round (x * 10 ^ (k - 1 - m)) / 10 ^ (k - 1 - m)`. This `m` is the decimal
exponent, the place `10 ^ m` of the leading significant digit, and the rounded value is `x` rounded
at the place `10 ^ (m + 1 - k)`, with ties broken by `round t = ⌊t + 1 / 2⌋`.
