# Wolsey's bound: tree plus minimum T-join costs at most 3/2 of the subtour LP

Let $(V,c)$ be a metric TSP instance on $n \ge 3$ vertices and let $x$ be an optimal solution of the subtour elimination LP. Then:

(i) $z=(1-\tfrac{1}{n})x \in P_{\mathrm{ST}}(K_V)$, so a minimum spanning tree $S^*$ satisfies $c(S^*) \le (1-\tfrac1n)\,c^{\top}x$.

(ii) For every $T \subseteq V$ with $|T|$ even, $\tfrac12 x \in P_T^{\uparrow}(K_V)$; by the Edmonds-Johnson theorem, which says that for $c \ge 0$ the minimum cost of a $T$-join equals $\min\{c^{\top}y : y \in P_T^{\uparrow}\}$, so that every point of the dominant upper-bounds the cost of an integral minimum $T$-join, a minimum-cost $T$-join $J$ has $c(J) \le \tfrac12 c^{\top}x$.

(iii) For every spanning tree $S$ with odd-degree set $T$ and every $T$-join $J$, the multigraph $S \uplus J$ is connected with all degrees even, hence Eulerian, and shortcutting an Euler tour gives a Hamiltonian cycle of cost at most $c(S)+c(J)$.

Consequently the Christofides-Serdyukov tour costs at most $(\tfrac32-\tfrac1n)\,\mathrm{OPT}_{\mathrm{LP}}$.

## Proof sketch

For (i), $x(E(S))=\tfrac12(2|S|-x(\delta(S))) \le |S|-1$ for every proper nonempty $S$ and $x(E)=n$, so $z(E)=n-1$; minimality of $S^*$ over $P_{\mathrm{ST}}$ gives the bound. For (ii), every $T$-odd set is a proper nonempty subset, so $\tfrac12 x(\delta(S)) \ge 1$. For (iii), adding $J$ flips exactly the parities at $T$, so all degrees become even, and the triangle inequality makes shortcutting non-increasing in cost. Summing (i) and (ii) gives the final bound.

## Depends on

- [Spanning tree polytope of a connected graph](spanning-tree-polytope.md)
- [Subtour elimination LP of a metric TSP instance](subtour-elimination-lp.md)
- [T-joins and the T-join dominant polyhedron](t-join-dominant.md)

## Proof depends on

- [Edmonds-Johnson theorem: a minimum T-join costs the minimum of the T-join dominant](edmonds-johnson-t-join-dominant.md)
- [Characterization of Eulerian indexed walks](../../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/is-eulerian-iff.md)
- [APPROX-TSP-TOUR on a given minimum spanning tree costs at most twice any tour](../../double-tree-approximation-for-metric-tsp/approx-tsptour-two-approx.md)
- [Handshake lemma for edge-indexed multigraphs](../../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/even-sum-degree.md)

## Sources

- Laurence A. Wolsey, "Heuristic Analysis, Linear Programming and Branch and Bound", Mathematical Programming Study 13 (1980).
- David B. Shmoys, David P. Williamson, "Analyzing the Held-Karp TSP Bound: A Monotonicity Property with Application", Information Processing Letters (1990).
- Jack Edmonds, Ellis L. Johnson, "Matching, Euler Tours and the Chinese Postman", Mathematical Programming (1973).
