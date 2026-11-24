# Level decomposition of the expected site-frequency spectrum under Λ-coalescents

Let $\Lambda \ne 0$ be a finite measure on $[0, 1]$ and $n \ge 2$. Let $(Y_t)$ be the block-counting process of the $\Lambda$-coalescent started from $n$ singletons, with jump rates $q_{ij} = \binom{i}{i-j+1}\lambda_{i,i-j+1}$ for $i > j \ge 1$ and embedded jump probabilities $p_{ij} = q_{ij}/(-q_{ii})$; let $g(n, m) = E_n\int_0^\infty \mathbf 1(Y_s = m)\,ds$ be the expected time it spends with $m$ blocks, so that $g(m, m) = 1/(-q_{mm})$ and $g(n, m) = \sum_{k=m}^{n-1} p_{nk}\,g(k, m)$ for $n > m \ge 2$; and let $p^{(n)}[k, i]$ be the probability that, given that there are at some time exactly $k$ branches, a given one of them subtends exactly $i$ of the $n$ leaves. Then for $1 \le i \le n - 1$ the [expected length](../../../../Biology/coalescent-theory/multiple-merger-coalescents/site-frequency-spectrum-under-coalescents/expected-length.md) of branches subtending $i$ copies satisfies
$$E[L_i] = \sum_{k=2}^{n-i+1} p^{(n)}[k, i]\cdot k\cdot g(n, k),$$
and hence the [expected site frequency spectrum](../../../../Biology/coalescent-theory/multiple-merger-coalescents/site-frequency-spectrum-under-coalescents/expected-sfs.md) is $E[\xi_i] = \frac\theta2\sum_{k=2}^{n-i+1} p^{(n)}[k, i]\cdot k\cdot g(n, k)$ (Birkner, Blath and Eldon 2013, Proposition 1.1 and eqs. (6)–(8)). The target is this level decomposition, with the recursion for $p^{(n)}[k, i]$ given in the source's appendix, as an identity with the first-step definition of the expected length.

## Depends on

- [Expected length of branches subtending i sample copies](../../../../Biology/coalescent-theory/multiple-merger-coalescents/site-frequency-spectrum-under-coalescents/expected-length.md)
- [Expected site frequency spectrum under a Λ-coalescent](../../../../Biology/coalescent-theory/multiple-merger-coalescents/site-frequency-spectrum-under-coalescents/expected-sfs.md)

## Expansion

1. The block-counting process of a $\Lambda$-coalescent and its [generator](../../../../Biology/coalescent-theory/coalescents/block-counting-generator.md).
2. The Green function $g(n, m)$ and its first-jump recursion.
3. The probability $p^{(n)}[k, i]$ and its recursion.
4. The level decomposition: summing, over the levels $k$, the expected time at level $k$ times the expected number $k\,p^{(n)}[k, i]$ of branches at that level subtending $i$ leaves, and its agreement with the occupation sum of the block-size jump chain.
5. The source's recursions for variances and covariances, and $\Xi$-coalescent analogues, as separate statements.

## Sources

- M. Birkner, J. Blath and B. Eldon, Statistical properties of the site-frequency spectrum associated with Λ-coalescents, Genetics 195 (2013), 1037–1053. <https://doi.org/10.1534/genetics.113.156612>
