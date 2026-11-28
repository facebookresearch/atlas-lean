# Every directed graph has a phi-expander decomposition whose backward edges number O(phi m log m)

Let $G=(V,E)$ be a directed unweighted graph with $m$ edges and $n$ vertices, and let $0<\phi\le 1$.

1. (Edge version.) There are a partition $\mathcal{X}=\{X_1,\dots,X_k\}$ of $V$ and an edge set $E^r\subseteq E$ with $|E^r|=O(\phi m\log m)$ such that each $G[X_i]$ is a $\phi$-expander and the graph $(G\setminus E^r)/\mathcal{X}$, obtained by deleting $E^r$ and contracting every $X_i$, is acyclic.
2. (Vertex version.) There is a partition $\{R,X_1,\dots,X_k\}$ of $V$ with $|R|=O(\phi n\log n)$ such that each $G[X_i]$ is a $\phi$-vertex expander (no partition $(A,S,B)$ of $X_i$ with $A,B\ne\emptyset$ and no edge of $G[X_i]$ from $A$ to $B$, or none from $B$ to $A$, has $|S|<\phi\min\{|A|,|B|\}$) and deleting $R$ and contracting each $X_i$ leaves an acyclic graph.

More generally, a pair $(\mathcal{X},E^r)$ with clusters that are $\phi$-expanders, $|E^r|\le\beta\phi m$, and $(G\setminus E^r)/\mathcal{X}$ acyclic is called a *$(\beta,\phi)$-expander decomposition*; item 1 asserts existence with $\beta=O(\log m)$.

## Proof sketch

Repeatedly find a $\phi$-sparse cut $(S,\bar S)$ in a current cluster, put the edges of the sparser direction into $E^r$, and recurse on both sides; stop when no cluster has a $\phi$-sparse cut. Order the clusters so that, at every cut, the side receiving the kept edges comes later; all surviving inter-cluster edges then go forward, so the contracted graph is acyclic. Charge the at most $\phi\min\{\mathrm{vol}(S),\mathrm{vol}(\bar S)\}$ removed edges to the smaller side; a vertex lies on the smaller side $O(\log m)$ times because the volume of its cluster halves each time, which gives $|E^r|=O(\phi m\log m)$. The vertex version is identical with vertex cuts and cardinalities.

## Depends on

- [Directed phi-expanders, phi-sparse directed cuts, and phi-expanding terminal edge sets](directed-phi-expanders.md)
- [Acyclic condensation](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/condensation-acyclic.md)
- [Embedding an expander with low vertex congestion certifies directed vertex expansion](vertex-expansion-by-low-congestion-embedding.md)

## Sources

- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental Reachability, SCC, and Shortest Paths via Directed Expanders and Congestion Balancing", FOCS (2020), arXiv:2009.02584.
- Aurelio L. Sulser, Maximilian Probst Gutenberg, "Near-Optimal Algorithm for Directed Expander Decompositions", ICALP (2025), LIPIcs 334, 132:1-132:20.
