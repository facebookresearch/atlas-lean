# Free-connex acyclic conjunctive queries

Let $Q$ be a conjunctive query with hypergraph $H(Q) = (V, E)$, whose vertices are the variables of $Q$ and whose edges are the
variable sets of its atoms, and let $\mathrm{free}(Q)$ be its set of free variables. $Q$ is *acyclic* if $H(Q)$ is acyclic, and
*free-connex* if both $H(Q)$ and the hypergraph $(V, E \cup \{\mathrm{free}(Q)\})$ are acyclic. A *head-path* of $Q$ is a
sequence of variables $(x, z_1, \dots, z_k, y)$ with $k \ge 1$, $x, y \in \mathrm{free}(Q)$, $z_1, \dots, z_k \notin \mathrm{free}(Q)$,
that is a chordless path in $H(Q)$: consecutive variables occur together in an atom and non-consecutive ones do not. An acyclic
conjunctive query has a head-path if and only if it is not free-connex.

## Depends on

- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Characterizations of acyclic database schemas](../../join-processing/characterizations-of-acyclic-database-schemas.md)
- [Join tree](../../join-processing/has-join-tree.md)

## Sources

- N. Carmeli and M. Kröll, "Enumeration complexity of conjunctive queries with functional dependencies", *Proceedings of ICDT 2018*; arXiv:1712.07880 <https://arxiv.org/abs/1712.07880>, Section 2 (classes of conjunctive queries), crediting the head-path characterization to Bagan, Durand and Grandjean.
