# Closed form of the drift kernel

For every real `x` and every natural number `b`, the [drift kernel](drift-kernel.md) satisfies
`x² D_b(x) = b x - 1 + (1 - x)^b`. For `0 ≤ x ≤ 1` the right side is the mean of `k - 1` for
`k` distributed as `Binomial(b, x)`, with the `k = 0` term removed.
