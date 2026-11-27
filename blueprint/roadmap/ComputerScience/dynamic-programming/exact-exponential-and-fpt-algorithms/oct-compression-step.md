# Odd cycle transversal compression via minimum vertex separators

Let $Z$ be an odd cycle transversal of a graph $G$ with $|Z| = k + 1$, and fix a proper $2$-colouring $f^*$ of $G - Z$. A *guess* splits $Z$ into a part $Z_0$ kept in the transversal and two parts $Z_1, Z_2$ that receive colours $1$ and $2$, with $Z_1$ and $Z_2$ independent in $G$; there are at most $3^{k+1}$ guesses. For a guess let $B_1 = N(Z_2) \setminus Z$ and $B_2 = N(Z_1) \setminus Z$, the vertices that must receive colour $1$, respectively $2$, unless deleted; let $B_c^* = (f^*)^{-1}(c)$; and let $C = (B_1 \cap B_2^*) \cup (B_2 \cap B_1^*)$ and $R = (B_1 \cap B_1^*) \cup (B_2 \cap B_2^*)$. Then $G$ has an odd cycle transversal $X'$ with $|X'| \le k$ and $X' \cap Z = Z_0$ such that some proper $2$-colouring of $G - X'$ gives colour $c$ to every vertex of $Z_c$ ($c = 1, 2$) if and only if some set $X \subseteq V(G) \setminus Z$ with $|X| \le k - |Z_0|$ separates $C$ from $R$ in $G - Z$, that is, no connected component of $G - Z - X$ contains both a vertex of $C \setminus X$ and a vertex of $R \setminus X$; then $X' = Z_0 \cup X$ is such a transversal. The separator avoids $Z$ but may contain vertices of $C \cup R$, and a minimum one is computed by maximum flow on the vertex-split network of $G - Z$ (Cygan et al., Lemmas 4.15 and 4.16).

## Proof sketch

A proper $2$-colouring of $G - Z - X$ that agrees with $B_1$ and $B_2$ extends to $G - X'$ by colouring $Z_c$ with $c$, since $Z_1, Z_2$ are independent and every neighbour outside $Z$ of $Z_1$ (of $Z_2$) has colour $2$ (colour $1$); conversely, a colouring of $G - X'$ as required restricts to one of $G - Z - X$ with $X = X' \setminus Z_0$. Comparing such a colouring with $f^*$, adjacent vertices outside $X$ either both keep or both change their colour, so each component of $G - Z - X$ keeps or flips $f^*$ as a whole; the vertices of $C$ must flip and those of $R$ must keep, which is possible exactly when no component meets both.

## Depends on

- [Iterative compression](iterative-compression.md)
- [Vertex cuts separating two vertices](../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/is-stvertex-cut.md)
- [Feasible odd cycle transversal instances](../../../TheoryOfComputation/np-completeness/graph-covering-and-domination/odd-cycle-transversal/odd-cycle-transversal-feasible.md)

## Sources

- B. Reed, K. Smith and A. Vetta, "Finding Odd Cycle Transversals", Operations Research Letters 32(4), 2004.
- F. Hüffner, "Algorithm Engineering for Optimal Graph Bipartization", Journal of Graph Algorithms and Applications 13(2), 2009.
- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
