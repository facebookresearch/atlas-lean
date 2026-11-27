# Odd cycle transversal compression via minimum vertex separators

Let $Z$ be an odd cycle transversal of a graph $G$ with $|Z| = k + 1$, and fix a proper $2$-colouring of $G - Z$. For each of the $3^{k+1}$ ways to split $Z$ into a part $Z_0$ kept in the transversal and two parts $Z_1, Z_2$ that receive colours $1$ and $2$ (with $Z_1$ and $Z_2$ independent and their colouring consistent), $G$ has an odd cycle transversal of size at most $k$ extending this guess if and only if a minimum vertex separator in $G - Z_0$ between two explicit terminal sets derived from $Z_1$, $Z_2$ and the colouring has size at most $k - |Z_0|$. Such a separator is computed by maximum flow on the vertex-split network.

## Proof sketch

In $G - Z$ every vertex is left or right of the fixed colouring; a new transversal $X$ disjoint from $Z_1 \cup Z_2$ must cut every path along which colour parity forces a conflict, which is exactly a vertex separation between the doubled terminal copies.

## Depends on

- [Iterative compression](iterative-compression.md)
- [Vertex cuts separating two vertices](../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/is-stvertex-cut.md)

## Sources

- B. Reed, K. Smith and A. Vetta, "Finding Odd Cycle Transversals", Operations Research Letters 32(4), 2004.
- F. Hüffner, "Algorithm Engineering for Optimal Graph Bipartization", Journal of Graph Algorithms and Applications 13(2), 2009.
- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
