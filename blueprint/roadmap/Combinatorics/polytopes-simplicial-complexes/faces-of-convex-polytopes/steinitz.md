# Steinitz's theorem

A finite simple graph $G$ is the graph of a 3-dimensional convex polytope if and only if $G$ is
planar and 3-connected.

Precisely: for a finite vertex set, $G$ is planar (has a crossing-free straight-line drawing in the
plane) and 3-vertex-connected (has more than 3 vertices and stays connected after deleting any
two vertices) if and only if there is a finite set $s \subset \mathbb{R}^3$ whose convex hull has
nonempty interior and whose polytope graph is isomorphic to $G$. Planarity with straight-line
edges is equivalent to topological planarity for finite simple graphs by Fáry's theorem, and the
3-connectivity condition forces at least 4 vertices, as for the tetrahedron.

The direction from polytopes to graphs is the easy one: planarity comes from a Schlegel diagram or
a stereographic projection, and 3-connectivity is the case $d = 3$ of Balinski's theorem. The hard
direction constructs a polytope from a 3-connected planar graph.

## Informally uses

- [Balinski's theorem](balinski.md): the case $d = 3$ gives the 3-connectivity of the graph of a
  3-polytope, in the easy direction.

## Sources

- G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Mathematics Series, Volume 14 (2004), arXiv:math/0411400v2 (7 December 2005). Numbering as in this arXiv version, which is the version read; the published version was not consulted. Theorem 1.2 and Section 1.2 (an informal statement of the bijection between 3-connected planar graphs and combinatorial types of 3-polytopes).
- E. Steinitz (1922), references [74] and [75] of the PCMI notes (not read).
