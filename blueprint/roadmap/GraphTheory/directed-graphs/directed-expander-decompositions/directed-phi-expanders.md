# Directed phi-expanders, phi-sparse directed cuts, and phi-expanding terminal edge sets

Let $G=(V,E)$ be a directed unweighted multigraph. For $S\subseteq V$ let $\mathrm{vol}(S)=\sum_{v\in S}\deg(v)$, where $\deg(v)$ counts both in- and out-edges, let $\bar S=V\setminus S$, and let $E(S,\bar S)$ be the set of edges from $S$ to $\bar S$. For $0<\phi\le 1$, a cut $\emptyset\ne S\subsetneq V$ is *$\phi$-sparse* if

$$
\min\{|E(S,\bar S)|,|E(\bar S,S)|\}<\phi\cdot\min\{\mathrm{vol}(S),\mathrm{vol}(\bar S)\},
$$

and $G$ is a *(directed) $\phi$-expander* if it has no $\phi$-sparse cut. Thus a directed expander must expand in both directions across every cut. For a set of *terminal edges* $F\subseteq E$, define $\deg_F(v)$ as the number of edges of $F$ incident to $v$ and $\mathrm{vol}_F(S)=\sum_{v\in S}\deg_F(v)$; $G$ is a *$\phi$-expander with respect to $F$* if no cut $S$ has $\min\{|E(S,\bar S)|,|E(\bar S,S)|\}<\phi\min\{\mathrm{vol}_F(S),\mathrm{vol}_F(\bar S)\}$. The set $F$ is *$\phi$-expanding in $G$* if for every strongly connected component $C$ of $G$ there is no cut $\emptyset\ne S\subsetneq C$ with $\min\{|E(S,C\setminus S)|,|E(C\setminus S,S)|\}<\phi\min\{\mathrm{vol}_F(S),\mathrm{vol}_F(C\setminus S)\}$, where $\deg_F$, and hence $\mathrm{vol}_F$, is still taken in $G$: it also counts the edges of $F$ that leave $C$.

## Depends on

- [Volume of a vertex set](../../algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/volume.md)
- [Strongly connected vertices](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md)
- [Cut capacity](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/cut-capacity.md)

## Sources

- Aaron Bernstein, Joakim Blikstad, Thatchaphol Saranurak, Ta-Wei Tu, "Maximum Flow by Augmenting Paths in n^(2+o(1)) Time", FOCS (2024), arXiv:2406.03648.
- Aaron Bernstein, Maximilian Probst Gutenberg, Thatchaphol Saranurak, "Deterministic Decremental Reachability, SCC, and Shortest Paths via Directed Expanders and Congestion Balancing", FOCS (2020), arXiv:2009.02584.
- Aurelio L. Sulser, Maximilian Probst Gutenberg, "Near-Optimal Algorithm for Directed Expander Decompositions", ICALP (2025), LIPIcs 334, 132:1-132:20.
