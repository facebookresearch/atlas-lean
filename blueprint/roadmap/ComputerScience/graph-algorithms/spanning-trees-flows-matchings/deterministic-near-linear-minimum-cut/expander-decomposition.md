# Weighted expander decompositions with volumes measured in the host graph

Let $G = (V, E, w)$ be an undirected graph with positive weights, weighted degrees $d(v)$ and volume $\mathrm{vol}(S) = \sum_{v \in S} d(v)$. For a vertex set $C$ and $\phi > 0$, the induced graph $G[C]$ is a *$\phi$-expander* if

$$
\frac{w(E(S, C \setminus S))}{\min(\mathrm{vol}(S), \mathrm{vol}(C \setminus S))} \ge \phi \quad \text{for every } \emptyset \ne S \subsetneq C,
$$

with volumes measured in $G$. A *$(\phi, \epsilon)$-expander decomposition* is a partition $V = C_1 \cup \dots \cup C_k$ such that every $G[C_i]$ is a $\phi$-expander and the total weight of edges between different clusters is at most $\epsilon \cdot \mathrm{vol}(V)$. This is the weighted analogue of *$(\varphi, \varepsilon)$-expander decompositions of an undirected graph*. The recursive sparse-cut argument of *Every graph has a phi-expander decomposition with O(phi m log m) crossing edges* gives, for every $\phi \in (0,1]$, such a decomposition with $\epsilon = O(\phi \log \mathrm{vol}(V))$.

## Depends on

- [Volume of a vertex set](../../../../GraphTheory/algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/volume.md)
- [Edge expansion of a vertex set](../../../../GraphTheory/algebraic-graph-theory/part-01/grassmann-graphs/untitled.md)
- [(phi, epsilon)-expander decompositions of an undirected graph](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/phi-epsilon-expander-decomposition.md)

## Sources

- Thatchaphol Saranurak, "A Simple Deterministic Algorithm for Edge Connectivity", SOSA (2021), arXiv:2008.08575.
- Jason Li, "Deterministic Mincut in Almost-Linear Time", STOC (2021), arXiv:2106.05513.
