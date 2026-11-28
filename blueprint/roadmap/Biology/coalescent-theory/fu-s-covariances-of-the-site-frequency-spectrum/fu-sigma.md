# Fu's covariance matrix $\sigma_{ij}$

For natural numbers `n`, `i` and `j`, Fu's (1995) `σ_{ij}` for the sample size `n` is defined from
[Fu's function](fu-beta.md) `β_n` and from `A(r) = (a_1(n) - a_1(r)) / (n - r)`, where
`a_1(r) = ∑_{k=1}^{r-1} 1/k` is [Tajima's constant](../segregating-sites-and-pairwise-differences/tajima-a1.md). On the diagonal,

* `σ_{ii} = β_n(i + 1)` if `2i < n`,
* `σ_{ii} = 2 A(i) - 1/i²` if `2i = n`,
* `σ_{ii} = β_n(i) - 1/i²` if `2i > n`;

off the diagonal (`i ≠ j`), with `u = max(i, j)` and `v = min(i, j)`,

* `σ_{ij} = (β_n(u + 1) - β_n(u)) / 2` if `i + j < n`,
* `σ_{ij} = A(u) + A(v) - (β_n(u) + β_n(v + 1)) / 2 - 1/(ij)` if `i + j = n`,
* `σ_{ij} = (β_n(v) - β_n(v + 1)) / 2 - 1/(ij)` if `i + j > n`.

The formula is [symmetric](fu-sigma-comm.md) in `i` and `j`. It is evaluated for all natural
numbers `n`, `i`, `j`, with the convention `x / 0 = 0` wherever a denominator vanishes. Fu's matrix
is its restriction to `1 ≤ i, j ≤ n - 1`, where no denominator vanishes and `β_n` is used only at
`1, …, n - 1`.

There, under Kingman's coalescent with an independent random-joining topology, `σ_{ij}` is a
quarter of the covariance of the lengths `L_i` and `L_j` of the branches subtending `i` and `j`
sample copies ([Fu's branch-length covariances](../fu-s-branch-length-covariances-for-every-sample/covariance-sfs-length-eq-four-mul-fu-sig.md)). With Poisson infinite-sites mutation
at rate `θ / 2` per unit branch length, it is also the coefficient of `θ²` in `Cov(ξ_i, ξ_j)`, the
covariance of the numbers of sites whose derived allele is carried by `i` and by `j` copies
([Fu's covariance of the site frequency spectrum](../fu-s-branch-length-covariances-for-every-sample/covariance-count-kingman-eq-fu-sigma.md)).
