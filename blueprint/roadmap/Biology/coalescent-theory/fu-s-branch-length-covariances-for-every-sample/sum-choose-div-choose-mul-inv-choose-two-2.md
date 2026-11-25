# Binomial-ratio sum for complementary sizes $i + j = n$

For natural numbers `n`, `i` and `j` with `i ≥ 1`, `j ≥ 1` and `i + j = n`,

`∑_{k=2}^{n} C(j, k - 1) / (C(n - 1, k - 1) C(k, 2))
= 2 (H_{n-1} - H_{i-1}) - 2n (H_n - H_{i-1}) / (n - i + 1) + 2`,

where `H_m = ∑_{k=1}^{m} 1/k` is the [harmonic number](harm.md) (`H_0 = 0`, used when `i = 1`). Here
`n - i + 1 = j + 1` is positive, the denominators `C(n - 1, k - 1) C(k, 2)` are positive for
`2 ≤ k ≤ n`, and binomial coefficients are extended by `C(u, v) = 0` for natural `v > u`, so the
terms with `k > j + 1` vanish.
