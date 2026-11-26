# (phi, epsilon)-expander decompositions of an undirected graph

Let $G = (V, E)$ be an undirected multigraph with $m$ edges and let $\varphi \in (0, 1]$, $\varepsilon \ge 0$. A partition $V = V_1 \sqcup \dots \sqcup V_k$ is a *$(\varphi, \varepsilon)$-expander decomposition* of $G$ if

1. $\Phi_{G[V_i]} \ge \varphi$ for every $i \in \{1, \dots, k\}$, and
2. $\sum_{i=1}^{k} \delta_G(V_i) \le \varepsilon m$, i.e. at most $\varepsilon m / 2$ edges join different clusters.

It is a *strong* decomposition if moreover $\Phi_{G\{V_i\}} \ge \varphi$ for every $i$, where $G\{V_i\}$ is the degree-preserving induced subgraph. The bicriteria trade-off is between the expansion $\varphi$ inside clusters and the fraction $\varepsilon$ of inter-cluster edges.

## Depends on

- [Cut conductance, phi-expanders and degree-preserving induced subgraphs](conductance-and-phi-expanders.md)

## Sources

- Thatchaphol Saranurak, Di Wang, "Expander Decomposition and Pruning: Faster, Stronger, and Simpler", SODA (2019), arXiv:1812.08958.
- Ravi Kannan, Santosh Vempala, Adrian Vetta, "On Clusterings: Good, Bad and Spectral", J. ACM 51(3) (2004).
