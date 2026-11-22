# Rounding place from the decimal exponent

If `10 ^ m ≤ |x| < 10 ^ (m + 1)`, rounding to `k` significant figures (for a positive
count `k : ℕ+`) rounds `x` at the decimal place `10 ^ (m + 1 - k)`.
