# Representations of matroids over division rings

A matroid is representable over a division ring when its ground set maps to a module over that ring so that exactly the independent sets go to linearly independent families; a matroid with such a representation over some division ring is skew-linear.

A *division ring* (skew field) $D$ is a ring with identity $1 \ne 0$ in which every nonzero element has a two-sided multiplicative inverse; a commutative division ring is a [field](../../../Algebra/rings-and-fields/field.md). Let $M = (E, r)$ be a [matroid](matroids-given-by-rank-functions.md). A *representation of $M$ over $D$* is a map from $E$ to a right $D$-module such that a subset of $E$ is independent in $M$ exactly when its image is linearly independent over $D$. $M$ is *representable over $D$* if it has such a representation, and *skew-linear* if it is representable over some division ring; representability over a field is the usual notion of a linear matroid.

## Depends on

- [Matroids given by rank functions](matroids-given-by-rank-functions.md)
- [Field](../../../Algebra/rings-and-fields/field.md)

## Proof depends on

None.

## Expansion

Every linear matroid is skew-linear. There are skew-linear matroids that are not linear, and indeed not multilinear (Theorem 6.1 of the source).

## Sources

- L. Kühne, R. Pendavingh and G. Yashfe, "Von Staudt constructions for skew-linear and multilinear matroids", *Combinatorial Theory* 3 (2023), no. 1, article 16, doi:10.5070/C63160429; read as arXiv:2012.07361v1, <https://arxiv.org/abs/2012.07361v1>: Definition 2.1 and the definitions following it in Section 2, and Theorem 6.1, of arXiv:2012.07361v1.
