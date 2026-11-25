# Dimension

The dimension of a finite-dimensional vector space $V$ over $\mathbb F = \mathbb R$ or $\mathbb C$, one spanned by
finitely many vectors, is the length of any basis of $V$: $V$ has a basis, and all its bases have the same length.

## Idea

Dimension counts independent directions: $\dim \mathbb F^n = n$, the polynomials of degree at most $m$ form a space of
dimension $m + 1$, and $\mathbb C$ has dimension $1$ as a vector space over $\mathbb C$ but $2$ over $\mathbb R$. That
all bases have the same length rests on one inequality: in a finite-dimensional space, a linearly independent list is
never longer than a spanning list. A subspace $U$ of $V$ is again finite-dimensional, with $\dim U \le \dim V$, and
$\dim U = \dim V$ only when $U = V$. Two finite-dimensional vector spaces over $\mathbb F$ are isomorphic exactly when
they have the same dimension. For a space that is not finite-dimensional, the cardinality of a basis, which is again the
same for all bases, plays the role of the dimension.

## Statements

- [Dimension of a finite-dimensional vector space](finite-dimension.md)
- [Finite-dimensional vector space](finite-dimensional.md): the spaces the definition applies to
- [Any two bases are indexed by sets of the same cardinality](mk-eq-mk-of-basis.md): makes the definition well posed, and the cardinality of a basis well defined for every vector space
- [Every subspace of a finite-dimensional space is finite-dimensional](finite-dimensional-submodule.md): every subspace then has a dimension, which the rank–nullity theorem needs for the null space
- [A linearly independent family is no larger than a finite spanning set](linear-independent-le-span.md): the inequality the definition rests on: in a space spanned by $n$ vectors, a linearly independent family has at most $n$ members; used in the proof
- [Nonzero commutative rings have the strong rank condition](comm-ring-strong-rank-condition.md): so that the bound on linearly independent families applies over every field; used in the proof
- [Nonzero commutative rings have invariant basis number](invariant-basis-number-of-nontrivial-of.md): so that all bases have the same cardinality over every field; used in the proof

## Background

- [Bases](../bases/README.md): bases as finite lists

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 2.35, with 2.9, 2.22, 2.25, 2.34, 2.36, 2.37, 2.39 and 3.70 (version read: the open-access PDF dated 4 November 2026).
