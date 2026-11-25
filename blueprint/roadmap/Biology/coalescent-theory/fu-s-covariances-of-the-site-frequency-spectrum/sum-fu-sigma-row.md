# Row sums of Fu's covariance matrix

For natural numbers `n` and `i` with `1 ≤ i ≤ n - 1`, row `i` of
[Fu's covariance matrix](fu-sigma.md) for the sample size `n` sums to

`∑_{j=1}^{n-1} σ_{ij} = (a_1(n) - a_1(i)) / (n - i)`,

where `a_1(r) = ∑_{k=1}^{r-1} 1/k` is [Tajima's constant](../segregating-sites-and-pairwise-differences/tajima-a1.md). The terms in
[Fu's function](fu-beta.md) `β_n` cancel in every such row.
