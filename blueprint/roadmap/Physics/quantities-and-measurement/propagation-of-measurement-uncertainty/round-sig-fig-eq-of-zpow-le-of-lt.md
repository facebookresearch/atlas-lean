# Rounding place from the decimal exponent

If `10 ^ m ≤ |x| < 10 ^ (m + 1)`, rounding to `k ≥ 1` significant figures rounds `x` at the decimal
place `10 ^ (m + 1 - k)`: the rounded value is `round (x * 10 ^ (k - 1 - m)) / 10 ^ (k - 1 - m)`.
