# One-generation sampling identity for Cannings partitions

In a [Cannings model](cannings-model.md) with population size $N$ and offspring vector $\nu = (\nu_1, \dots, \nu_N)$, sample $b \le N$ distinct children of one generation and let $\pi$ be the partition of $[b]$ by common parent, with blocks $B_1, \dots, B_a$ (singletons included). Then

$$P_N(\pi) = \frac{(N)_a}{(N)_b}\, \mathbb{E}\Bigl[\prod_{j=1}^{a} (\nu_j)_{|B_j|}\Bigr],$$

where $(x)_k = x(x - 1) \cdots (x - k + 1)$ is the falling factorial. The proof sums over ordered tuples of distinct parents, whose terms are equal by the exchangeability of parents, and uses the exchangeability of children for the sample.

In particular, the probability that two sampled children share a parent is $P_N(\{1, 2\}) = \mathbb{E}[(\nu_1)_2]/(N - 1) = c_N$, and $\sum_{\pi} P_N(\pi) = 1$ over the partitions of $[b]$.

## Depends on

- [Cannings model](cannings-model.md)

## Expansion

1. The identity, from the exchangeability of parents and of children.
2. The case $b = 2$, which gives the pair-coalescence probability $c_N$.
3. A sweepstake example: with probability $c_N$ all children choose one uniform parent, and otherwise parents are a uniform bijection. Then $P_N(\{1,2\}\{3\}) = 0$ and $P_N(\{1,2,3\}) = c_N$ exactly.
4. A check that the five partitions of $[3]$ have probabilities summing to $1$.

## Sources

- M. Möhle and S. Sagitov, A classification of coalescent processes for haploid exchangeable population models, *Ann. Probab.* 29 (2001), 1547–1562, <https://doi.org/10.1214/aop/1015345761> (sampling identities).
