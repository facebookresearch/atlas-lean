# The common ancestor of a subsample is that of the whole sample with probability (n+1)(m−1)/((n−1)(m+1))

Let $2 \le m \le n$ and let the genealogy of $n$ genes follow [random joining](random-joining.md). For a fixed set of $m$ of the genes, the most recent
common ancestor of the $m$ genes is the most recent common ancestor of all $n$ with probability

$$\frac{(n + 1)(m - 1)}{(n - 1)(m + 1)} ;$$

this equals $1$ when $m = n$, equals $(n + 1)/(3(n - 1))$ when $m = 2$, and for every $m$ it equals the
[probability $p_{n,m}$ that a pair is still in separate lineages](../segregating-sites-and-pairwise-differences/pair-separate-prob.md) while $m$ lineages remain, and tends to $(m - 1)/(m + 1)$ as
$n \to \infty$.

The two subtrees below the root contain $K$ and $n - K$ of the genes, where $K$ is uniform on $\{1, \dots, n - 1\}$
(in forward time each of the current lineages is equally likely to be the next to split, so the numbers of lineages
on the two sides of the root evolve as a Pólya urn started from one lineage on each side). The subsample's ancestor is the root exactly when the subsample meets both
subtrees, and, since the random-joining law is invariant under relabelling the genes, given $K = k$ the genes below one side of
the root form a uniformly random $k$-subset, so the subsample lies inside a given subtree of size $k$ with probability
$\binom km / \binom nm$. Summing over both sides, the probability is

$$1 - \frac{2}{n - 1} \sum_{k=m}^{n-1} \frac{\binom km}{\binom nm} = 1 - \frac{2}{n - 1} \cdot \frac{\binom n{m+1}}{\binom nm} = 1 - \frac{2 (n - m)}{(n - 1)(m + 1)} .$$

## Depends on

- [Random joining](random-joining.md)
- [Probability that a pair lies in separate lineages](../segregating-sites-and-pairwise-differences/pair-separate-prob.md)

## Sources

- I. W. Saunders, S. Tavaré and G. A. Watterson, "On the genealogy of nested subsamples from a haploid population", Advances in Applied Probability 16 (1984), 471–491, <https://doi.org/10.2307/1427285>, Corollary 4 (p. 477), whose case $l = 1$ is this probability for a subsample of size $j = m$ of a sample of size $i = n$. The derivation above is self-contained.
