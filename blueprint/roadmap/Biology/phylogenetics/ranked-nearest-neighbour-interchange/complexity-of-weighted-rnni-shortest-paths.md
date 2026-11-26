# Complexity of shortest paths in the weighted RNNI graph

In the [weighted graph $\mathrm{RNNI}(\rho)$](rnni-graph-of-ranked-phylogenetic-trees.md), rank moves cost $\rho \ge 0$ and NNI moves cost $1$. Let $\mathrm{RNNI}(\rho)$-SP be the problem of computing a minimum-weight path between two given ranked trees.

**Theorem.** $\mathrm{RNNI}(0)$-SP is NP-hard.

**Proposition.** For every $\rho \ne 1$ the FindPath algorithm does not in general compute shortest paths in $\mathrm{RNNI}(\rho)$.

Together with the [quadratic-time solution for $\rho = 1$](findpath-computes-rnni-shortest-paths.md), the complexity of the shortest path problem therefore depends on $\rho$, ranging from quadratic to NP-hard.

## Depends on

- [RNNI graph of ranked phylogenetic trees](rnni-graph-of-ranked-phylogenetic-trees.md)
- [FindPath computes RNNI shortest paths in quadratic time](findpath-computes-rnni-shortest-paths.md)

## Expansion

When $\rho = 0$ rank moves are free, so the distance equals the minimum number of NNI moves converting the underlying unranked topologies, with NNI allowed on every edge; this is the classical NNI distance, which is NP-hard to compute (DasGupta et al. 2000). The counterexamples for $\rho \neq 1$ are explicit four-leaf trees. For $\rho > 1$, from $T = [\{a_1,a_2\}, \{a_1,a_2,a_3\}, \{a_1,\dots,a_4\}]$ to $R = [\{a_3,a_4\}, \{a_2,a_3,a_4\}, \{a_1,\dots,a_4\}]$ FindPath uses two NNI moves and one rank move (weight $2 + \rho$), while a path of three NNI moves has weight $3$. For $\rho < 1$, from $[\{a_1,a_2\}, \{a_3,a_4\}, \{a_1,\dots,a_4\}]$ to $[\{a_1,a_3\}, \{a_1,a_3,a_4\}, \{a_1,\dots,a_4\}]$ FindPath uses three NNI moves (weight $3$), while one rank move followed by two NNI moves has weight $2 + \rho$. Characterizing the threshold values of $\rho$ at which the problem changes complexity class is left open.

## Sources

- L. Collienne and A. Gavryushkin, "Computing nearest neighbour interchange distances between ranked phylogenetic trees", *Journal of Mathematical Biology* 82 (2021), article 8, <https://doi.org/10.1007/s00285-021-01567-5> (PMC7835203; Theorem 2 and Proposition 2).
