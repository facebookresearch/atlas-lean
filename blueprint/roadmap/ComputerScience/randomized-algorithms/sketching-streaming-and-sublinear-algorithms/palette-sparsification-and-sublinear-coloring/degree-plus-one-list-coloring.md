# The (deg + 1)-list-coloring problem (D1LC)

An instance of *$(\deg + 1)$-list-coloring* (D1LC) is a finite simple graph $G = (V, E)$ with $n$ vertices together with lists $S(v)$, $v \in V$, of colors with $|S(v)| \ge \deg(v) + 1$. A solution is a proper coloring $\chi$ with $\chi(v) \in S(v)$ for all $v$. Some sources require lists of exactly $\deg(v) + 1$ colors. The two conventions are interchangeable: an exact-size instance is an instance of the general one, and truncating every list of a general instance to $\deg(v) + 1$ colors gives an exact-size instance each of whose solutions solves the original one. Every instance is solvable by the greedy algorithm in any vertex order, because when $v$ is processed at most $\deg(v)$ colors of $S(v)$ are blocked. Neither this nor the solution condition uses connectivity or vertex identifiers: a disconnected graph is colored componentwise, and the truncated lists use at most $\sum_v (\deg(v) + 1) \le n^2$ colors, which can be renamed to $\{1, \dots, n^2\}$, so assuming a color space of size $\mathrm{poly}(n)$, as distributed models do, loses no generality. D1LC generalizes $(\Delta + 1)$-coloring (all lists equal to $\{1, \dots, \Delta + 1\}$, truncated in the exact-size convention). Removing colored vertices and deleting their colors from their neighbors' lists leaves a D1LC instance on the uncolored vertices; in the exact-size convention, truncate the lists again afterwards.

## Depends on

- [The LIST COLORING decision problem](../../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/list-coloring/list-coloring-dec.md)

## Sources

- Magnús M. Halldórsson, Fabian Kuhn, Alexandre Nolin, Tigran Tonoyan, "Near-Optimal Distributed Degree+1 Coloring", STOC (2022), arXiv:2112.00604.
- Noga Alon, Sepehr Assadi, "Palette Sparsification Beyond (Delta+1) Vertex Coloring", APPROX/RANDOM (2020), arXiv:2006.10456.
- M. Ghaffari, F. Kuhn, "Deterministic Distributed Vertex Coloring: Simpler, Faster, and without Network Decomposition", FOCS 2021, arXiv:2011.04511.
