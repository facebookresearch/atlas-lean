# Fully dynamic alpha-approximate maximum matching and its value version

Let $G_t = (V, E_t)$, $|V| = n$, be a graph undergoing an online sequence of edge insertions and deletions, and let $\mu(G)$ denote the maximum size of a matching of $G$. For $\alpha \ge 1$:

1. an *$\alpha$-approximate dynamic matching algorithm* maintains after every update a matching $M_t \subseteq E_t$ with $|M_t| \ge \mu(G_t)/\alpha$;
2. an *$\alpha$-approximate matching-size algorithm* (value version) maintains a number $\nu_t$ with $\mu(G_t)/\alpha \le \nu_t \le \mu(G_t)$.

Guarantees are stated for a fixed adversary model (oblivious or adaptive) and with amortized or worst-case update time. A maximal matching is a $2$-approximation, which can be maintained deterministically in $O(n)$ worst-case time per update, and the main open problem is whether a $(1+\varepsilon)$-approximation, or any ratio below $2$, can be maintained in polylogarithmic update time.

## Depends on

- [The augmenting-path maximum matching](../../maximum-bipartite-matching/max-matching.md)
- [Approximation algorithms and approximation ratios](../../../../approximation-algorithms/approximation-algorithms-and-approximation-ratios.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
- Sayan Bhattacharya, Peter Kiss, Thatchaphol Saranurak, "Dynamic (1+epsilon)-Approximate Matching Size in Truly Sublinear Update Time", FOCS (2023), arXiv:2302.05030.
- Mohammad Roghani, Amin Saberi, David Wajc, "Beating the Folklore Algorithm for Dynamic Matching", ITCS (2022), arXiv:2106.10321.
