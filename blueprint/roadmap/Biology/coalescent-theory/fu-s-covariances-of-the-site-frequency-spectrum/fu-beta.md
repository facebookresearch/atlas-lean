# Fu's auxiliary function $\beta_n(i)$

For natural numbers `n` and `i`, Fu's (1995) function is

`β_n(i) = 2n / ((n - i + 1)(n - i)) · (a_1(n + 1) - a_1(i)) - 2 / (n - i)`,

where `a_1(m) = ∑_{k=1}^{m-1} 1/k` is [Tajima's constant](../segregating-sites-and-pairwise-differences/tajima-a1.md). Its intended domain is
`1 ≤ i ≤ n - 1`, where no denominator vanishes: these are the arguments at which
[Fu's covariance matrix](fu-sigma.md) uses it for `1 ≤ i, j ≤ n - 1`. The formula is evaluated for
all natural numbers `n` and `i`, with the convention `x / 0 = 0`; so `β_n(n) = 0` and
`β_n(n + 1) = 2`.
