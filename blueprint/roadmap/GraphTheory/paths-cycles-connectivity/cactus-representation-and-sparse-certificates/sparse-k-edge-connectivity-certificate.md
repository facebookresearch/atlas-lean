# Sparse k-edge-connectivity certificates and forest decompositions

Let $G = (V, E)$ be an undirected multigraph and $k \ge 1$ an integer. A spanning subgraph $H \subseteq G$ is a *$k$-edge-connectivity certificate* of $G$ if for all distinct $x, y \in V$

$$
\lambda_H(x, y) \ge \min\{\lambda_G(x, y), k\},
$$

equivalently (by Menger's theorem) $|\partial_H S| \ge \min\{|\partial_G S|, k\}$ for every $S \subseteq V$. A *forest decomposition* of $G$ is a sequence $F_1, F_2, \dots$ of edge-disjoint forests where $F_1$ is a maximal spanning forest of $G$ and $F_i$ is a maximal spanning forest of $G - (E(F_1) \cup \dots \cup E(F_{i-1}))$; write $G_k = F_1 \cup \dots \cup F_k$.

## Depends on

- [Spanning forest of an input graph](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/kruskal-s-algorithm/is-spanning-forest.md)
- [Edge cuts separating two vertices](../menger-s-theorem/is-stedge-cut.md)

## Sources

- Hiroshi Nagamochi, Toshihide Ibaraki, "A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph", Algorithmica (1992).
- C. Chekuri, C. Xu, "Computing Minimum Cuts in Hypergraphs", arXiv:1607.08682v3, Section 1.1 (local-connectivity form $\lambda_{G'}(s,t) \ge \min\{k, \lambda_G(s,t)\}$).
- G. Bezdrighin, M. Elkin, M. Ghaffari, C. Grunau, B. Haeupler, S. Ilchi, V. Rozhoň, "Deterministic Distributed Sparse and Ultra-Sparse Spanners and Connectivity Certificates", arXiv:2204.14086v2, Appendix G (cut form).
- K. Kawarabayashi, M. Thorup, "Deterministic Edge Connectivity in Near-Linear Time", arXiv:1411.5123v5, Section 6.2 (maximal forest decomposition).
- D. Panigrahi, Duke COMPSCI 590.1 Graph Algorithms, Lecture 7 (2015), Definition 4 (greedy spanning forest packing).
