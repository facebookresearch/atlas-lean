# Pseudo-cube trees for multiclass universal rates

Let $H \subseteq Y^X$ with $Y$ countable. A **Daniely–Shalev-Shwartz–Littlestone (DSL) tree** is an infinite tree in which a node at level $k$ is labelled by a tuple $x_u \in X^{k+1}$ together with a finite $(k+1)$-dimensional pseudo-cube $B_u \subseteq Y^{k+1}$ (a nonempty finite set of label vectors in which every vector has, in every coordinate $i$, a neighbour in $B_u$ that differs from it exactly in coordinate $i$); the children of $u$ are indexed by the vectors of $B_u$, and every finite path is required to be realized by a concept of $H$ that agrees with all chosen label vectors on all chosen tuples. Analogously, a **multiclass Littlestone tree** branches at each node over pairs of distinct labels, and a **Natarajan–Littlestone (NL) tree** and **Graph–Littlestone (GL) tree** branch over Natarajan-shattered and graph-shattered tuples respectively.

## Depends on

- [VCL trees and the VCL dimension](vcl-tree.md)
- [k-pseudo-cubes and the k-DS dimension](../list-learning-and-multiclass-pseudo-cubes/k-pseudo-cube.md)
- [N-shattering](../../../../../not-yet-classified/natarajan/nshatters.md)

## Sources

- S. Hanneke, S. Moran, Q. Zhang, "Universal Rates for Multiclass Learning", COLT (2023), arXiv:2307.02066.
- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550.
