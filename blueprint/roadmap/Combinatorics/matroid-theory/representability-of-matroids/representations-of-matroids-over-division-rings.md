# Representations of matroids over division rings

A matroid is representable over a division ring when its ground set maps to a module over that ring so that exactly the independent sets go to linearly independent families; a matroid with such a representation over some division ring is skew-linear.

A *division ring* (skew field) $D$ is a ring with identity $1 \ne 0$ in which every nonzero element has a two-sided multiplicative inverse; a commutative division ring is a [field](../../../Algebra/rings-and-fields/field.md). Let $M = (E, r)$ be a [matroid](matroids-given-by-rank-functions.md). A *representation of $M$ over $D$* is a map $\varphi$ from $E$ to a right $D$-module $A$ such that a subset $S \subseteq E$ is independent in $M$ exactly when the family $(\varphi(e))_{e \in S}$, indexed by $S$, is linearly independent over $D$; a right $D$-module is a left module over the opposite ring $D^{\mathrm{op}}$, and linear independence is taken there. Indexing by $S$ matters: two elements of $S$ with the same image make the family dependent. $M$ is *representable over $D$* if it has such a representation, and *skew-linear* if it is representable over some division ring; representability over a field is the usual notion of a linear matroid.

## Depends on

- [Matroids](matroids-given-by-rank-functions.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Module over a semiring](../../../Algebra/modules/module.md)
- [Linearly independent family](../../../LinearAlgebra/bases-and-dimension/bases-and-coordinates/bases/linear-independent.md)

## Proof depends on

None.

## Expansion

Every linear matroid is skew-linear. There are skew-linear matroids that are not linear, and indeed not multilinear (Theorem 6.1 of the source).

## Sources

- L. Kühne, R. Pendavingh and G. Yashfe, "Von Staudt constructions for skew-linear and multilinear matroids", *Combinatorial Theory* 3 (2023), no. 1, article 16, doi:10.5070/C63160429; read as arXiv:2012.07361v1, <https://arxiv.org/abs/2012.07361v1>: Definition 2.1 and the definitions following it in Section 2, and Theorem 6.1, of arXiv:2012.07361v1.
