# Coefficient of $\beta_n(i)$ in Fu's half covariance

For natural numbers `n`, `i` and `j`,

`A_n(i, j) = [i < j] + [i = j] + [i + j < n] (n - i - j + 1) / j`,

where `[P]` is `1` if `P` holds and `0` otherwise. With the convention `x / 0 = 0`, the last term
is `0` when `j = 0`, so `A_n(i, 0)` is `1` if `i = 0` and `0` otherwise; the intended domain is
`1 ≤ i, j ≤ n - 1`. It is the first of four coefficients in the closed form of the
[level moments](level-moment.md): in [Fu's half covariance](fu-half-cov.md) it multiplies Fu's
`β_n(i)`.
