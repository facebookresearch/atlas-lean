# Watterson's $\theta^2$ coefficient from Fu's closed form

For every natural number `n`, the entries of [Fu's covariance matrix](fu-sigma.md) for the sample
size `n` sum to [Tajima's constant](../segregating-sites-and-pairwise-differences/tajima-a2.md) `a_2(n) = ∑_{k=1}^{n-1} 1/k²`:

`∑_{i=1}^{n-1} ∑_{j=1}^{n-1} σ_{ij} = a_2(n)`

(both sides are `0` for `n ≤ 1`). This `a_2(n)` is the coefficient of `θ²` in Watterson's (1975)
[variance of the number of segregating sites](../segregating-sites-and-pairwise-differences/variance-seg-sites.md), `Var S = θ a_1(n) + θ² a_2(n)` with
`a_1(n) = ∑_{k=1}^{n-1} 1/k`. For branch lengths with `Cov(L_i, L_j) = 4 σ_{ij}` for all
`1 ≤ i, j ≤ n - 1`, it gives `Var(L_1 + ⋯ + L_{n-1}) = 4 a_2(n)`
([variance of the summed branch lengths](variance-sum-sfs-length-one-of-fu-sigma.md)).
