# Planar split networks represent exactly the flat split systems

**Setting.** A *split* $A|B$ of a finite set $X$ is a bipartition, and a *split system* is a set of splits of $X$. A *pseudoline* is a curve in the plane homeomorphic to a line; a *pseudoline arrangement* is a finite set of pseudolines in which every two cross in exactly one point. Placing the elements of $X$ as points off all pseudolines, each pseudoline induces a split of $X$. A split system is *flat* if it is induced in this way by some pseudoline arrangement (and *affine* if straight lines suffice). A *split network* is a partial cube (isometric subgraph of a hypercube) with some vertices labelled by $X$; removing all edges of one parallel class leaves two components and so induces a split of $X$. It is *planar* if it has a straight-line drawing with the edges of each class parallel and of equal length, edges meeting only at endpoints, strictly convex internal faces, and at least one edge of every class on the outer face.

**Theorem.** For a split system $\mathcal S$ on a finite set $X$ the following are equivalent:

1. $\mathcal S$ is flat;
2. $\mathcal S$ is induced by a planar split network partially labelled by $X$;
3. $\mathcal S$ is encoded by a loop-free, acyclic oriented matroid of rank $3$ on $X$, that is, every $A|B\in\mathcal S$ equals $T^+|T^-$ for some tope $T$ of that matroid.

## Expansion

Flat systems and rank-$3$ oriented matroids correspond through the Folkman–Lawrence topological representation theorem, after adding a pseudoline that leaves all points and crossings on one side. From an arrangement to a network: the dual graph of the arrangement is a partial cube, and the Bohne–Dress theorem on zonotopal tilings yields a drawing in which each class is a family of parallel, equal-length edges with convex cells. Conversely, the classes of a planar split network trace out curves that form a pseudoline arrangement inducing the same splits. Circular split systems, the outer-labelled case produced by Neighbor-Net, are the special case with all labelled vertices on the outer face.

## Sources

- M. Balvočiūtė, D. Bryant and A. Spillner, *When can splits be drawn in the plane?*, arXiv:1509.06104 (2015). <https://doi.org/10.48550/arXiv.1509.06104> Main theorem and definitions of flat, planar and oriented-matroid-encoded split systems (Section 2), with its proof (Section 3). The paper's results are unnumbered. Published version: SIAM Journal on Discrete Mathematics 31 (2017) 839–856, <https://doi.org/10.1137/15m1040852>.
