# Rounding to significant figures is well defined

For `x ≠ 0` and a count `k ≥ 1`, the textbook description determines the rounding of `x` to `k`
significant figures: there is exactly one decimal exponent `m` (the place `10 ^ m` of the leading
significant digit) with `10 ^ m ≤ |x| < 10 ^ (m + 1)`, and for it the rounded value is
`round (x * 10 ^ (k - 1 - m)) / 10 ^ (k - 1 - m)`, `x` rounded at the place `10 ^ (m + 1 - k)`, with
ties broken by `round t = ⌊t + 1 / 2⌋`.
