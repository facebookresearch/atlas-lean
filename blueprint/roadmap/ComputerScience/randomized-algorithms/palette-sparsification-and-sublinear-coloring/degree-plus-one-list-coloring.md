# The (deg + 1)-list-coloring problem (D1LC)

An instance of *$(\deg + 1)$-list-coloring* (D1LC) is a simple graph $G = (V, E)$ together with lists $S(v)$, $v \in V$, where $S(v)$ is an arbitrary set of exactly $\deg(v) + 1$ colors. A solution is a proper coloring $\chi$ with $\chi(v) \in S(v)$ for all $v$. Every instance is solvable by the greedy algorithm in any vertex order, because when $v$ is processed at most $\deg(v)$ colors of $S(v)$ are blocked. D1LC generalizes $(\Delta + 1)$-coloring (all lists equal to $\{1, \dots, \Delta + 1\}$, after truncation) and is closed under removing colored vertices and their colors from neighbors' lists.

## Depends on

- [The LIST COLORING decision problem](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/list-coloring/list-coloring-dec.md)
- [Palette sparsification experiment, sampled lists and the conflict graph](palette-sparsification-experiment.md)

## Sources

- Magnús M. Halldórsson, Fabian Kuhn, Alexandre Nolin, Tigran Tonoyan, "Near-Optimal Distributed Degree+1 Coloring", STOC (2022), arXiv:2112.00604.
- Noga Alon, Sepehr Assadi, "Palette Sparsification Beyond (Delta+1) Vertex Coloring", APPROX/RANDOM (2020), arXiv:2006.10456.
