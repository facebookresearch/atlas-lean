# Existence of bases

Every vector space $V$ over a division ring $K$, in particular over a field, has a basis: there is a basis of $V$
indexed by a subset of $V$.

## Idea

A basis is a linearly independent family that spans $V$; every vector is then a finite linear combination of basis
vectors in exactly one way. For a space spanned by finitely many vectors, deleting redundant vectors from a spanning list
leaves a basis. In general the proof uses Zorn's lemma, a form of the axiom of choice: among the linearly independent
sets there is a maximal one, and it spans $V$, since a vector outside its span could be adjoined without losing
independence. The same argument gives a stronger form: inside any set $t$ of vectors, every linearly independent subset
extends to a linearly independent subset of $t$ whose span contains $t$.

## Statements

- [Every vector space has a basis](exists-basis.md)
- [Adjoining a vector outside the span preserves linear independence](insert.md): used in the proof
- [Extending a linearly independent set within a larger set](exists-linear-indep-on-extension.md): a stronger form, from which the existence of bases follows with $t$ the whole space

## Background

- [Bases](../bases/README.md): bases of finite-dimensional spaces, as finite lists

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 2.31 and 2.32, for finite-dimensional spaces (version read: the open-access PDF dated 4 November 2026).
