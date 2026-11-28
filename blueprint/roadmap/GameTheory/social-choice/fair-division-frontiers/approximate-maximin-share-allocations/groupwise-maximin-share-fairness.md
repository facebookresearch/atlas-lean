# Groupwise maximin share fairness

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For a complete allocation $X$ and a nonempty set of agents $S \subseteq N$, the maximin share of $i \in S$ restricted to $S$ is $\mu_i^S(X) = \max \min_{k \in S} v_i(P_k)$, the maximum over partitions $(P_k)_{k \in S}$ of $\bigcup_{k \in S} X_k$ into $\lvert S\rvert$ bundles. For $\alpha \in (0, 1]$, $X$ is $\alpha$-GMMS if $v_i(X_i) \ge \alpha\, \mu_i^S(X)$ for every $S$ and every $i \in S$. The case of two-element sets $S$ is $\alpha$-pairwise maximin share fairness, and $S = N$ recovers $\alpha$-MMS.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Sources

- S. Barman, A. Biswas, S. K. Krishnamurthy, Y. Narahari, "Groupwise Maximin Fair Allocation of Indivisible Goods", AAAI 2018, arXiv:1711.07621.
- G. Amanatidis, E. Markakis, A. Ntokos, "Multiple Birds with One Stone: Beating 1/2 for EFX and GMMS via Envy Cycle Elimination", AAAI 2020; Theoretical Computer Science 841 (2020), arXiv:1909.07650.
