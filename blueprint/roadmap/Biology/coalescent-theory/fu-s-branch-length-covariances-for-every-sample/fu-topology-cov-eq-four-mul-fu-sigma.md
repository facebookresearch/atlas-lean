# Fu's topology identity for every sample size

For every natural number `n` and all `i`, `j` with `1 ≤ i, j ≤ n - 1`,

`F_n(i, j) = 4 σ_{ij}`,

where `σ_{ij}` is [Fu's closed form](../fu-s-covariances-of-the-site-frequency-spectrum/fu-sigma.md) and `F_n(i, j)` is
[Fu's topology covariance](../branch-length-covariances-from-random-joining/fu-topology-cov.md),

`F_n(i, j) = ∑_{k=2}^{n} ∑_{l=2}^{n} E[c_{k,i} c_{l,j}] t(k, l) - m_i m_j`, with
`m_i = ∑_{k=2}^{n} E[c_{k,i}] / C(k, 2)`.

Here `c_{k,i}` is the number of blocks of size `i` while `k` lineages remain under random joining
from `n` singletons, whose moments are given by iterates of the random-joining transition
operator, and `t(k, l)` is `2 / C(k, 2)²` if `k = l` and `1 / (C(k, 2) C(l, 2))` otherwise. Both
sides are deterministic numbers. The
[identity for samples of size at most 4](../branch-length-covariances-from-random-joining/fu-topology-cov-eq-four-mul-fu-sigma-of.md) is a
special case.
