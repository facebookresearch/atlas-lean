# Fu's topology covariance through level moments

For natural numbers `n`, `i` and `j` with `1 ≤ i < n` and `1 ≤ j < n`,

`F_n(i, j) = S_n(i, j) + S_n(j, i) - (2 / i)(2 / j)`, where
`S_n(i, j) = ∑_{k=2}^{n} C(k, 2)⁻¹ M_n(k; i, j)`,

`M_n` is the [level moment](level-moment.md) and `F_n(i, j)` is
[Fu's topology covariance](../branch-length-covariances-from-random-joining/fu-topology-cov.md),

`F_n(i, j) = ∑_{k=2}^{n} ∑_{l=2}^{n} E[c_{k,i} c_{l,j}] t(k, l) - m_i m_j`, with
`m_i = ∑_{k=2}^{n} E[c_{k,i}] / C(k, 2)`.

Here `c_{k,i}` is the number of blocks of size `i` while `k` lineages remain under random joining
from `n` singletons, whose moments are given by iterates of the random-joining transition
operator, and `t(k, l)` is `2 / C(k, 2)²` if `k = l` and `1 / (C(k, 2) C(l, 2))` otherwise, the
second moments of the holding times of Kingman's coalescent. The term `(2 / i)(2 / j)` is
`m_i m_j`: the expected branch lengths are `m_i = 2 / i` and `m_j = 2 / j`.
