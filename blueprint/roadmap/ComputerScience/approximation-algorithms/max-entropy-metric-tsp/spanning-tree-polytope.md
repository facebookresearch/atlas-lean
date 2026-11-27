# Spanning tree polytope of a connected graph

Let $G=(V,E)$ be a connected edge-indexed multigraph (parallel edges are distinct elements of $E$, loops are excluded) with $n=|V| \ge 2$. A spanning tree of $G$ is a set $T \subseteq E$ of $n-1$ edges containing no cycle, so that $(V,T)$ is connected; it contains at most one edge from each class of parallel edges. For $S \subseteq V$ let $E(S)$ denote the set of edges with both endpoints in $S$, and for $z \in \mathbb{R}^E$ and $F \subseteq E$ write $z(F)=\sum_{e \in F} z_e$. The spanning tree polytope of $G$ is

$$
P_{\mathrm{ST}}(G)=\{z \in \mathbb{R}_{\ge 0}^{E} : z(E)=n-1,\ z(E(S)) \le |S|-1 \ \text{for all}\ \emptyset \ne S \subsetneq V\}.
$$

Edmonds showed that $P_{\mathrm{ST}}(G)$ is the convex hull of the indicator vectors $\mathbf{1}_T$ of the spanning trees $T$ of $G$: it is the base polytope of the graphic matroid of $G$, whose bases are the spanning trees, and the proof shows by linear programming duality that the matroid greedy algorithm produces integral optimal primal and dual solutions. Consequently, for every cost vector $c \in \mathbb{R}^E$, the minimum cost of a spanning tree equals $\min\{c^{\top}z : z \in P_{\mathrm{ST}}(G)\}$.

## Depends on

- [Edge-indexed multigraph](../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/edge-indexed-multigraph.md)

## Proof depends on

- [Optimality of the matroid greedy algorithm](../../greedy-algorithms-and-matroids/matroid-greedy-algorithm/matroid-greedy-optimal.md)
- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- Jack Edmonds, "Matroids and the Greedy Algorithm", Mathematical Programming (1971).
- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Section 2.2, equation (2).
