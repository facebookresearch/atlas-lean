# Dynamic (1+eps)-approximate matching size in truly sublinear update time

For every constant $\varepsilon > 0$ there is a randomized fully dynamic algorithm that maintains a $(1+\varepsilon)$-approximation of the maximum matching size of a graph with $n$ vertices and $m$ edges in worst-case update time $m^{0.5 - \Omega_{\varepsilon}(1)}$, with high probability against an adaptive adversary. This is the first polynomial improvement over the $O(n)$ bound obtained by periodic recomputation. The key subroutine is a sublinear-time algorithm computing a $(1, \varepsilon n)$-approximation (additive error $\varepsilon n$) of the maximum matching size on dense graphs.

## Proof sketch

Recomputing a near-maximum matching every $\varepsilon\mu$ updates handles the regime where $\mu$ is large compared with $\sqrt{m}$, so the hard case is when $\mu$ is near $n$ on dense graphs. There, an additive $\varepsilon n$ estimate suffices, and the new sublinear algorithm obtains it by simulating augmenting-path searches of bounded length with adjacency-matrix queries. Amortized over the stable period, the sublinear estimator costs $m^{0.5-\Omega_\varepsilon(1)}$ per update, deamortized by background recomputation.

## Depends on

- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Proof depends on

- [Gupta-Peng: (1+eps)-approximate dynamic matching in O(sqrt(m) eps^{-2}) worst-case update time](gupta-peng-dynamic-matching.md)

## Sources

- Sayan Bhattacharya, Peter Kiss, Thatchaphol Saranurak, "Dynamic (1+epsilon)-Approximate Matching Size in Truly Sublinear Update Time", FOCS (2023), arXiv:2302.05030.
- Manoj Gupta, Richard Peng, "Fully Dynamic (1+epsilon)-Approximate Matchings", FOCS (2013), arXiv:1304.0378.
