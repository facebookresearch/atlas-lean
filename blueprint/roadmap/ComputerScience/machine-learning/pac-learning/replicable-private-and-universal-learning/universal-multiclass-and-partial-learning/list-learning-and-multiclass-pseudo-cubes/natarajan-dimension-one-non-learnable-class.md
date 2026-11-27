# A non-learnable class of Natarajan dimension one

There is a label set $Y$ and a class $H \subseteq Y^X$ with Natarajan dimension $1$ and infinite DS dimension; consequently $H$ is not PAC learnable. The construction identifies $d$-dimensional pseudo-cubes with $(d-1)$-dimensional properly colored pure simplicial complexes in which every codimension-one face lies in exactly two facets, and shows that a pseudo-cube built from a complex with no empty squares has Natarajan dimension at most $1$. Such complexes of every dimension are provided by the hyperbolic pseudo-manifolds of Januszkiewicz and Świątkowski.

## Proof sketch

A pseudo-cube in $Y^d$ corresponds to a colored complex whose vertices are (coordinate, label) pairs and whose facets are the label vectors; the neighbour condition is exactly the pseudo-manifold condition. A Natarajan-shattered pair of coordinates corresponds to a square $v_0 v_1 v_2 v_3$ in the complex with alternating colors, and if the complex has no empty squares there is no such square, so the Natarajan dimension is at most one. Taking the disjoint union over $d$ of such pseudo-cubes on disjoint coordinate sets gives infinite DS dimension, hence non-learnability.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)
- [N-shattering](../../../../../not-yet-classified/natarajan/nshatters.md)
- [DS dimension characterizes multiclass PAC learnability](../../../ds-dimension-characterizes-multiclass-pac-learnability.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550.
