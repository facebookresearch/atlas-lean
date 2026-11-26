# Topology and rank of the Penner–Waterman poset of $k$-noncrossing RNA structures

**Diagrams.** An RNA structure on bases $1, \dots, n$ is encoded by a diagram: arcs $(i, j)$, $i < j$, join paired bases. A base in no arc is a *free site*. The diagram is *$k$-noncrossing* if it has no $k + 1$ pairwise crossing arcs ($k = 1$: secondary structures; $k \ge 2$: pseudoknots), and *binary* if each base lies in at most one arc. An arc is *tautological* if it covers exactly one free site, or if some arc below it covers the same set of free sites. A diagram is *regular* if no two crossing arcs are both incident with the same interval of consecutive non-free sites.

**Penner–Waterman poset.** For $k \ge 1$, $f \ge 3$ and $r \ge 0$, let $\mathcal{P}^r_{f,k}$ be the set of regular binary $k$-noncrossing diagrams with exactly $f$ free sites and at most $r$ tautological arcs, ordered by *arc suppression* (deleting an arc together with its two endpoints). For $k = 1$ this is Penner and Waterman's poset $\mathcal{P}^r_f$ of secondary structures, and $\mathcal{P}^0_f$ is isomorphic to the poset of triangulations of an $(f+1)$-gon.

**Theorem.** Let $f \ge 3$, $k \ge 1$ and $f \ge 2k$.

1. The geometric realization of $\mathcal{P}^0_{f,k}$ (its order complex) is the join of a simplicial sphere of dimension $k(f - 2k) - 1$ and an $\big((f+1)(k-1) - 1\big)$-simplex.
2. For every $r \ge 0$, $\mathcal{P}^r_{f,k}$ is pure (all maximal chains have the same length) and has rank $k(2f - 2k + 1) + r - f - 1$.

For $k = 1$ the simplex factor is empty and item 1 recovers the Penner–Waterman theorem that the space of RNA secondary structures with $f$ free sites and no tautological arcs is a sphere of dimension $f - 3$.

## Expansion

A *block* is a maximal interval of non-free sites; with $f$ free sites there are $f + 1$ possible block positions, and each proper diagram (binary, every arc covering at least one but not all free sites) is mapped to a symmetric integer *block matrix* of order $f + 1$ encoding the incidences between blocks given by its arcs; two diagrams with the same block matrix differ only by a bijection of arcs preserving the free sites below each arc, and each class contains exactly one regular diagram. This gives a poset isomorphism between $\mathcal{P}^r_{f,k}$ and a poset of symmetric matrices, and for $r = 0$ further with the poset $\mathcal{S}_{f+1,k}$ of all (not necessarily binary) $k$-noncrossing diagrams on $f + 1$ free sites. Arcs of such diagrams are diagonals of an $(f+1)$-gon with no $k+1$ pairwise crossing, i.e. partial $k$-triangulations; the $k$-relevant diagonals form a simplicial sphere of dimension $k(f - 2k) - 1$ (the multiassociahedron), and the $(f+1)(k-1)$ $k$-irrelevant short diagonals, which may be present or absent freely, contribute the simplex factor.

## Sources

- V. Moulton, T. Wu, "Posets and spaces of $k$-noncrossing RNA structures", arXiv:2204.05934 (2022): Section 1 (Penner–Waterman poset, the two main theorems on the geometric realization and on purity and rank, outline of the proof), Sections 3–7 (block matrices and regular diagrams, equivalence of diagrams, canonical representatives, poset isomorphisms), Section 8 (spaces of $k$-noncrossing diagrams via multitriangulations). <https://doi.org/10.48550/arXiv.2204.05934>
