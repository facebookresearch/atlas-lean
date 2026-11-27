# A non-learnable class of Natarajan dimension one

There is a label set $Y$ and a class $H \subseteq Y^X$ with Natarajan dimension $1$ and infinite DS dimension; consequently $H$ is not PAC learnable, since finite DS dimension is necessary for learnability. The construction reads a $d$-dimensional pseudo-cube as a properly $d$-colored pure simplicial complex (labels are vertices, label vectors are facets), uses that the Natarajan dimension is $1$ when the complex has no 4-cycle with alternating colors, and obtains suitable complexes of every dimension from the hyperbolic pseudo-manifolds of Januszkiewicz and Świątkowski.

## Proof sketch

A finite set $B \subseteq Y^d$ corresponds to a $d$-colored complex whose vertices are (coordinate, label) pairs and whose facets are the label vectors; $B$ is a pseudo-cube exactly when every codimension-one face of a facet lies in at least one other facet, which holds in a pseudo-manifold. Two coordinates N-shattered by $B$ give a 4-cycle whose vertices alternate between the two colors, so a complex without such cycles yields a pseudo-cube of Natarajan dimension $1$ (in dimension $3$, a suitable triangulation of the torus already works). Placing such pseudo-cubes for all $d$ on disjoint blocks of coordinates gives infinite DS dimension and Natarajan dimension $1$.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)
- [N-shattering](../../../../../not-yet-classified/natarajan/nshatters.md)

## Proof depends on

- [DS dimension characterizes multiclass PAC learnability](../../../ds-dimension-characterizes-multiclass-pac-learnability.md)

## Sources

- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550, Theorem 2, Figure 2, Section 5 and Proposition 43.
