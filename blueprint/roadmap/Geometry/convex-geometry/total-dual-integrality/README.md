# Total dual integrality

A linear system $A x \le b$ is *totally dual integral* (TDI) if for every integral objective $c$ for which $\max\{c^\top x : A x \le b\}$ is finite, the dual linear program $\min\{b^\top y : y \ge 0,\ A^\top y = c\}$ has an integral optimal solution. TDI is a property of the inequality system, not of the polyhedron: every rational polyhedron has a TDI description with integral $A$ (Goemans, Theorem 3), but $b$ is then integral only for integral polyhedra. The Edmonds–Giles theorem is the converse direction that makes TDI useful: TDI with integral $b$ forces every vertex to be integral, so a min-max relation with integral dual solutions proves an integral polyhedral description. Edmonds' matching polytope is the model example: by the Cunningham–Marsh formula (Schrijver, *A Course in Combinatorial Optimization*, Theorem 5.7) Edmonds' system has integral optimal dual solutions for integral weights. The older route to integral polyhedra is total unimodularity of the constraint matrix: if $A$ is totally unimodular and $b$ is integral, $\{x : A x \le b\}$ is integral (Schrijver, Theorem 8.1; the Hoffman–Kruskal theorem, his Corollary 8.2a, characterises total unimodularity this way). The incidence matrix of a graph is totally unimodular exactly when the graph is bipartite (Schrijver, Theorem 8.3), so Edmonds' system for non-bipartite graphs is not totally unimodular, which is where the dual-side notion is needed.

- [Totally dual integral system](is-tdi.md)
- [Upper-bound systems are totally dual integral](is-tdi-upper-bound.md)
- [Edmonds–Giles theorem](extreme-points-integral-of-is-tdi.md)

## Related topics

- [Linear programming](../linear-programming/README.md): TDI is a statement about integral optimal solutions of the dual linear program.
- [Matching polytope](../../../GraphTheory/matchings-and-flows/matching-polytope/README.md): Edmonds' description of the matching polytope, the model example of a totally dual integral system.
