# Rank–nullity theorem

Let $V$ and $W$ be vector spaces over $\mathbb F = \mathbb R$ or $\mathbb C$, with $V$ finite-dimensional, and let
$T \colon V \to W$ be a linear map. Then the range of $T$ is finite-dimensional and
$\dim V = \dim \operatorname{null} T + \dim \operatorname{range} T$.

## Idea

With $\operatorname{rank} T = \dim \operatorname{range} T$ and $\operatorname{nullity} T = \dim \operatorname{null} T$,
rank plus nullity is the dimension of the domain: what $T$ sends to $0$ and what it keeps add up to all of $V$. The proof
extends a basis of the null space to a basis of $V$; the images of the added vectors form a basis of the range. So a
linear map to a space of smaller dimension is not injective, which gives a nonzero solution to every homogeneous system
of linear equations with more unknowns than equations; a linear map to a space of larger dimension is not surjective;
and a linear map between spaces of the same finite dimension is injective exactly when it is surjective. For example,
for $m \ge 1$, differentiation on the polynomials of degree at most $m$ has the constants as null space and the
polynomials of degree at most $m - 1$ as range, and $m + 1 = 1 + m$. The theorem is also called the dimension theorem
or the fundamental theorem of linear maps.

## Statements

- [Rank–nullity theorem](rank-nullity.md)

## Background

- [Dimension](../../../bases-and-dimension/bases-and-coordinates/dimension/README.md): dimension of a finite-dimensional vector space

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 3.21, with 3.22, 3.24, 3.26 and 3.65 (version read: the open-access PDF dated 4 November 2026).
