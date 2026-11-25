# Edmonds' perfect matching polytope theorem

For a finite graph $G = (V, E)$, the [perfect matching polytope](perfect-matching-polytope.md) is the set of $x \in \mathbb{R}^E$ with

$$
x_e \ge 0 \ (e \in E), \qquad \sum_{e \ni v} x_e = 1 \ (v \in V), \qquad \sum_{e \in \delta(U)} x_e \ge 1 \ (U \subseteq V,\ |U| \text{ odd}),
$$

where $\delta(U)$ is the set of edges with exactly one end in $U$. Every perfect matching meets $\delta(U)$ for odd $U$, so the polytope lies in this set; the content of the theorem is the reverse inclusion. Schrijver derives it from the min-max relation produced by Edmonds' weighted matching algorithm (his Theorem 5.6) and linear programming duality.

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization* (CWI lecture notes), <https://homepages.cwi.nl/~lex/files/dict.pdf>, §5.4, Corollary 5.6a, constraints (27) and (28).
- J. Edmonds, *Maximum matching and a polyhedron with 0,1-vertices*, J. Res. Nat. Bur. Standards 69B (1965), 125–130.
