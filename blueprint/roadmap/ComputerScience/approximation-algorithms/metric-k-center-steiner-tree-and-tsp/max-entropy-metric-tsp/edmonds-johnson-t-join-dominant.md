# Edmonds-Johnson theorem: a minimum T-join costs the minimum of the T-join dominant

Let $G = (V, E)$ be a finite undirected graph, let $T \subseteq V$ with $|T|$ even, and let $c : E \to \mathbb{R}_{\ge 0}$. Then

$$
\min\{c(J) : J \ \text{a}\ T\text{-join of}\ G\} = \min\{c^{\top} y : y \in P_T^{\uparrow}(G)\},
$$

where both sides are $+\infty$ exactly when some connected component $C$ of $G$ contains an odd number of vertices of $T$ (then $C$ is a $T$-odd set with $\delta(C) = \emptyset$, so $P_T^{\uparrow}(G)$ is empty, and no $T$-join exists). Since $c \ge 0$, the minimum on the left may be taken over $T$-joins that are edge sets. Equivalently, the $T$-join dominant is integral:

$$
P_T^{\uparrow}(G) = \mathrm{conv}\{\mathbf{1}_J : J \subseteq E \ \text{a}\ T\text{-join}\} + \mathbb{R}_{\ge 0}^{E},
$$

so every point $y$ of the dominant satisfies $c^{\top} y \ge c(J)$ for a minimum-cost $T$-join $J$. When every connected component of $G$ contains an even number of vertices of $T$, the common value is finite and, by linear programming duality, equals the maximum, which is attained, of $\sum_S z_S$ over nonnegative weights $z$ on the $T$-odd sets $S$ with $\sum_{S : e \in \delta(S)} z_S \le c(e)$ for every edge $e$. Without this parity condition the packing problem is unbounded: a component $C$ with an odd number of vertices of $T$ (an isolated vertex of $T$, say) is a $T$-odd set with $\delta(C) = \emptyset$, so $z_C$ is unconstrained.

## Proof sketch

If some component of $G$ contains an odd number of vertices of $T$, both sides are $+\infty$; assume otherwise, so that $T$-joins exist. Every $T$-join lies in the dominant, so the left side is at least the right side. With $c \ge 0$, an inclusion-minimal $T$-join is the edge-disjoint union of $|T|/2$ paths pairing up the vertices of $T$, so the minimum cost of a $T$-join is the minimum cost of a perfect matching of $T$ under shortest-path distances. Edmonds and Johnson prove the reverse inequality with the blossom method behind Edmonds' perfect matching polytope theorem: a primal-dual algorithm outputs a $T$-join $J$ together with a packing $z$ of $T$-odd cuts satisfying the constraints above with $\sum_S z_S = c(J)$, and weak duality gives $c^{\top} y \ge \sum_S z_S$ for every $y \in P_T^{\uparrow}(G)$. The polyhedral form follows by separation: both sides of the second equation are closed convex sets closed under adding $\mathbb{R}_{\ge 0}^{E}$, and their minima agree for every $c \ge 0$.

## Depends on

- [T-joins and the T-join dominant polyhedron](t-join-dominant.md)

## Proof depends on

- [Edmonds' perfect matching polytope theorem](../../../../GraphTheory/matchings-and-flows/matching-polytope/perfect-matching-polytope-eq.md)

## Sources

- Jack Edmonds, Ellis L. Johnson, "Matching, Euler Tours and the Chinese Postman", Mathematical Programming 5 (1973), 88-124.
- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Proposition 2.3.
