# Dimension of a finite-dimensional vector space

Let $V$ be a finite-dimensional vector space over $\mathbb F$, where $\mathbb F$ is $\mathbb R$ or $\mathbb C$, that
is, a vector space spanned by some list of finitely many vectors. The dimension of $V$, written $\dim V$, is the length
of any basis of $V$. It is well defined: $V$ has a basis, and any two bases of $V$ have the same length.

## Proof

The field $\mathbb F$, like every commutative ring with $0 \neq 1$, has the strong rank condition and invariant basis
number, so the two facts on bases used below apply over $\mathbb F$. By the existence of bases, $V$ has a basis
$(b_i)_{i \in s}$ indexed by some set $s$; its vectors form a linearly independent family. If $V$ is spanned by a list
of $n$ vectors, these vectors form a finite set of at most $n$ elements that spans $V$, and a linearly independent
family in $V$ has at most as many members as such a set. So $s$ has at most $n$ elements, and the basis can be written
as a list. Any two bases of $V$ are indexed by sets of the same cardinality, so any two bases written as lists have the
same length.

## Depends on

- [Basis of a vector space](../bases/vector-space-basis.md)
- [Finite-dimensional vector space](finite-dimensional.md)

## Proof depends on

- [Every vector space has a basis](../existence-of-bases/exists-basis.md)
- [A linearly independent family is no larger than a finite spanning set](linear-independent-le-span.md)
- [Any two bases are indexed by sets of the same cardinality](mk-eq-mk-of-basis.md)
- [Nonzero commutative rings have the strong rank condition](comm-ring-strong-rank-condition.md)
- [Nonzero commutative rings have invariant basis number](invariant-basis-number-of-nontrivial-of.md)

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 2.35, with 2.9, 2.22, 2.31 and 2.34 (version read: the open-access PDF dated 4 November 2026).
