# Gupta-Peng: (1+eps)-approximate dynamic matching in O(sqrt(m) eps^{-2}) worst-case update time

For every constant $0 < \varepsilon < 1/2$ there is a deterministic data structure that maintains a $(1 + \varepsilon)$-approximate maximum matching of a graph with at most $m$ edges under edge insertions and deletions in worst-case time $O(\sqrt{m}\,\varepsilon^{-2})$ per update. For constant $\varepsilon$ and integer edge weights in $[1, N]$, a $(1+\varepsilon)$-approximate maximum weight matching can be maintained in $O(\sqrt{m}\log N)$ time per update.

## Proof sketch

A matching that is $(1+\varepsilon)$-approximate stays $(1 + O(\varepsilon))$-approximate for $\varepsilon\mu$ further updates, so a static $O(m/\varepsilon)$-time approximation algorithm can be rerun every $\varepsilon\mu$ updates, spread over those updates. When $\mu$ is small the graph is first trimmed to an equivalent subgraph of size $O(\mu^2)$ by discarding edges at vertices of very high degree, so that the rebuild cost per update is $O(\min\{m, \mu^2\}/(\varepsilon^2\mu)) = O(\sqrt{m}\varepsilon^{-2})$.

## Depends on

- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)

## Proof depends on

- [The augmenting-path maximum matching](../../maximum-bipartite-matching/max-matching.md)

## Sources

- Manoj Gupta, Richard Peng, "Fully Dynamic (1+epsilon)-Approximate Matchings", FOCS (2013), arXiv:1304.0378, Theorems 1.1 and 1.3 and Section 3.2.
