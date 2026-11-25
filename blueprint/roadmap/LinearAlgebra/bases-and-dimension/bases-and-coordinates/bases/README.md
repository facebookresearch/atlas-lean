# Bases

In the finite-list convention, a basis of a vector space $V$ over $\mathbb F = \mathbb R$ or $\mathbb C$ is a finite
list $v_1, \dots, v_n$ of vectors of $V$ that is linearly independent, meaning that $a_1 v_1 + \dots + a_n v_n = 0$ only
when every $a_k$ is $0$, and spans $V$, meaning that every vector of $V$ is a linear combination of $v_1, \dots, v_n$.

## Idea

A list is a basis exactly when every vector $v$ of $V$ can be written as $v = a_1 v_1 + \dots + a_n v_n$ in exactly one
way; the scalars $a_1, \dots, a_n$ are the coordinates of $v$, and they identify $V$ with $\mathbb F^n$. For example
$(1, 0), (0, 1)$ and $(1, 2), (3, 5)$ are bases of $\mathbb F^2$, and $1, z, \dots, z^m$ is a basis of the space of
polynomials of degree at most $m$. In a space spanned by finitely many vectors, every spanning list can be shortened to
a basis and every linearly independent list can be lengthened to one, and all bases have the same length, the
dimension. Linear independence makes sense for a family of vectors indexed by any set, and bases indexed by infinite
sets extend the notion to every vector space, such as the space of all polynomials, which has no finite basis.

## Statements

- [Basis of a vector space](vector-space-basis.md)
- [Linearly independent family](linear-independent.md): linear independence of a family indexed by any set, over any semiring

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 2.26, with 2.15, 2.27, 2.28, 2.30 and 2.32 (version read: the open-access PDF dated 4 November 2026).
