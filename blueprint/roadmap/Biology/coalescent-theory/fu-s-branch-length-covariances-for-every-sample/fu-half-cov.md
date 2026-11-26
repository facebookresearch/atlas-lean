# Fu's half covariance in closed form

For natural numbers `n`, `i` and `j`, Fu's half covariance is

`h_n(i, j) = 2 (A β_n(i) + B β' + C γ + D δ)`,

where `[P]` is `1` if `P` holds and `0` otherwise and

- `A = [i < j] + [i = j] + [i + j < n] (n - i - j + 1) / j` (the [first coefficient](coef-a.md)),
- `B = -[i < j] - [i + j < n] (n - i - j - 1) / j`,
- `C = -[i + j < n] / j` and `D = [i + j = n] / j`,
- `β' = β_n(i + 1)` if `i + 1 < n` and `β' = 0` otherwise,
- `γ = 2 / (i + j)` if `i + j < n` and `γ = 0` otherwise,
- `δ = 2 (H_{n-1} - H_{i-1}) - 2n (H_n - H_{i-1}) / (n - i + 1) + 2`,

where Fu's `β_n(i) = 2n (a_{n+1} - a_i) / ((n - i + 1)(n - i)) - 2 / (n - i)` uses
`a_m = ∑_{k=1}^{m-1} 1/k`, and `H_m = ∑_{k=1}^{m} 1/k` are the [harmonic numbers](harm.md). It is
defined for all `n`, `i` and `j`, with the convention `x / 0 = 0` (at `j = 0`, `B = C = D = 0` and
`A` is `1` if `i = 0` and `0` otherwise) and truncated `n - 1` and `i - 1` (`H_{i-1} = H_0 = 0`
at `i = 0`); the intended domain is `1 ≤ i, j ≤ n - 1`, where every denominator above is positive.

For `1 ≤ i, j ≤ n - 1` it equals `∑_{k=2}^{n} C(k, 2)⁻¹ M_n(k; i, j)`, the
[level moments](level-moment.md) weighted by the mean holding times `1 / C(k, 2)`: the part of
[Fu's topology covariance](../branch-length-covariances-from-random-joining/fu-topology-cov.md) before symmetrisation in `i` and `j`.
