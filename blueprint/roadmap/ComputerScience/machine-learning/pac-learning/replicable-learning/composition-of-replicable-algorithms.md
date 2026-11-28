# Composition of replicable algorithms

Replicable algorithms compose adaptively: a sequence of $k$ adaptively chosen $\rho$-replicable algorithms, each run on its own sample with its own shared randomness and each chosen in view of the earlier outputs, yields a transcript that is $O(k\rho)$-replicable (Bun, Gaboardi, Hopkins, Impagliazzo, Lei, Pitassi, Sivakumar and Sorrell, Section 1.4, item 3, attributing the result to Impagliazzo, Lei, Pitassi and Sorrell, Lemma A.7).

## Proof sketch

Couple two runs of the composite on independent samples with the same shared randomness; they produce different transcripts only if, at some stage, the earlier outputs agree and the current algorithm disagrees, which a union bound over the $k$ stages bounds by $k\rho$ (the hybrid argument of Impagliazzo, Lei, Pitassi and Sorrell, Lemma A.7, which compares fresh samples per query with one reused sample).

Derived (not stated in the cited sources):

1. (Padding.) Running an $m$-sample algorithm on the first $m$ of $m' \ge m$ samples preserves its output distribution and its disagreement probability.
2. (Adaptive sequential composition.) If $A_1$ is $\rho_1$-replicable over $\mathcal{D}$ on $m_1$ samples and, for every possible output $a$ of $A_1$, the algorithm $A_2(a)$ with an independent shared seed is $\rho_2$-replicable over $\mathcal{D}$ on $m_2$ samples, then running $A_1$ on the first $m_1$ samples and $A_2(a)$ on the next $m_2$ samples is $(\rho_1 + \rho_2)$-replicable, whether it outputs the pair or only the second result: splitting $m_1 + m_2$ i.i.d. draws into two blocks gives two independent i.i.d. samples, the shared seeds of the stages are independent, and the two coupled runs disagree only if the first stages disagree, or the first stages agree on some $a$ and the second stages disagree.
3. (Block composition.) Running $k$ algorithms $A_j$, each $\rho_j$-replicable, on $k$ disjoint blocks of samples with independent shared seeds is $\sum_j \rho_j$-replicable, and its single-run output is the product of the individual outputs; this follows from item 2 by induction.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)

## Sources

- M. Bun, M. Gaboardi, M. Hopkins, R. Impagliazzo, R. Lei, T. Pitassi, S. Sivakumar and J. Sorrell, "Stability is Stable: Connections between Replicability, Privacy, and Adaptive Generalization", Proceedings of the 55th Annual ACM Symposium on Theory of Computing (STOC), 2023, Section 1.4, item 3; open copy: <https://arxiv.org/abs/2303.12921>.
- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022, Lemma A.7 (arXiv version 1: <https://arxiv.org/abs/2201.08430v1>).
