# The equational theory of KAT is PSPACE-complete

Deciding whether an equation $p = q$ between terms holds in all [Kleene algebras with tests](kleene-algebras-with-tests.md) is PSPACE-complete. Membership in PSPACE follows from the [guarded-string characterization](guarded-strings-are-complete-for-kat.md): $G(p) \subseteq G(q)$ is tested by a nondeterministic search for a guarded string in $G(p) \setminus G(q)$ through automata built from the terms, using polynomial space. PSPACE-hardness is inherited from the equational theory of Kleene algebra.

## Depends on

- [Kleene algebras with tests](kleene-algebras-with-tests.md)
- [Polynomial space for decision problems](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Guarded strings are complete for Kleene algebra with tests](guarded-strings-are-complete-for-kat.md)

## Sources

- E. Cohen, D. Kozen and F. Smith, *The Complexity of Kleene Algebra with Tests*, technical report, Cornell University, 1996, <https://www.cs.cornell.edu/~kozen/Papers/ckat.pdf>, Section 5, Theorem 12.
