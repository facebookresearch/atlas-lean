# Composition of replicable algorithms

1. (Padding.) Running an $m$-sample algorithm on the first $m$ of $m' \ge m$ samples preserves its output distribution and its disagreement probability.
2. (Adaptive sequential composition.) If $A_1$ is $\rho_1$-replicable over $\mathcal{D}$ on $m_1$ samples and, for every possible output $a$ of $A_1$, the algorithm $A_2(a)$ with an independent shared seed is $\rho_2$-replicable over $\mathcal{D}$ on $m_2$ samples, then running $A_1$ on the first $m_1$ samples and $A_2(a)$ on the next $m_2$ samples is $(\rho_1 + \rho_2)$-replicable, whether it outputs the pair or only the second result.
3. (Block composition.) Running $k$ algorithms $A_j$, each $\rho_j$-replicable, on $k$ disjoint blocks of samples with independent shared seeds is $\sum_j \rho_j$-replicable, and its single-run output is the product of the individual outputs.

## Proof sketch

Splitting $m_1 + m_2$ i.i.d. draws into two blocks gives two independent i.i.d. samples, and shared seeds of the stages are independent. Two coupled runs of the composite disagree only if the first stages disagree, or the first stages agree on some $a$ and the second stages disagree; a union bound gives $\rho_1 + \rho_2$, and induction gives the block case.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022.
