# In an acyclic graph every partition into directed expanders consists of edgeless clusters

Let $G=(V,E)$ be an acyclic directed graph with $m$ edges, let $\phi>0$, and let $V=X_1\sqcup\dots\sqcup X_k$ be a partition such that every induced subgraph $G[X_i]$ is a $\phi$-expander. Then no $G[X_i]$ contains an edge, so all $m$ edges join distinct clusters. In particular, for the transitive tournament on $n$ vertices, every such partition has $m=\binom n2$ inter-cluster edges. Hence, unlike the undirected case, a directed expander decomposition cannot bound the number of inter-cluster edges by $\tilde O(\phi m)$; it can only bound the edges that go backward in a topological order of the clusters.

## Proof sketch

Suppose $G[X]$ has an edge and fix a topological order of $G[X]$. Let $v$ be the last vertex in this order with positive degree in $G[X]$; any out-edge of $v$ would point to a later vertex, which would then have positive degree, so $v$ has no out-edge in $G[X]$. Taking $S=\{v\}$ gives $E(S,\bar S)=\emptyset$ while $\mathrm{vol}(S)\ge 1$ and $\mathrm{vol}(X\setminus S)\ge 1$, since the other endpoint of an in-edge of $v$ lies in $X\setminus S$. Thus $S$ is a $\phi$-sparse cut of $G[X]$, a contradiction.

## Depends on

- [Directed phi-expanders, phi-sparse directed cuts, and phi-expanding terminal edge sets](directed-phi-expanders.md)
- [Acyclic condensation](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/condensation-acyclic.md)

## Sources

- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental Reachability, SCC, and Shortest Paths via Directed Expanders and Congestion Balancing", FOCS (2020), arXiv:2009.02584.
- Aurelio L. Sulser, Maximilian Probst Gutenberg, "Near-Optimal Algorithm for Directed Expander Decompositions", ICALP (2025), LIPIcs 334, 132:1-132:20.
