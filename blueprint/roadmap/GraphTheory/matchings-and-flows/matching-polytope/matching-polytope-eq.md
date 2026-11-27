# Edmonds' matching polytope theorem

For a finite graph $G = (V, E)$, the [matching polytope](matching-polytope.md) is the set of $x \in \mathbb{R}^E$ with

$$
x_e \ge 0 \ (e \in E), \qquad \sum_{e \ni v} x_e \le 1 \ (v \in V), \qquad \sum_{e \subseteq U} x_e \le \Bigl\lfloor \tfrac{|U|}{2} \Bigr\rfloor \ (U \subseteq V,\ |U| \text{ odd}).
$$

A matching has at most $\lfloor |U|/2 \rfloor$ edges inside $U$, so the polytope lies in this set; the theorem is the reverse inclusion. Schrijver leaves the derivation from the [perfect matching polytope theorem](perfect-matching-polytope-eq.md) as an exercise (his Exercise 5.21).

## Informally uses

- [Edmonds' perfect matching polytope theorem](perfect-matching-polytope-eq.md): Schrijver derives this theorem from it.

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization* (CWI lecture notes), <https://homepages.cwi.nl/~lex/files/dict.pdf>, §5.4, Corollary 5.6b, constraints (30), and Exercise 5.21.
- J. Edmonds, *Maximum matching and a polyhedron with 0,1-vertices*, J. Res. Nat. Bur. Standards 69B (1965), 125–130.
