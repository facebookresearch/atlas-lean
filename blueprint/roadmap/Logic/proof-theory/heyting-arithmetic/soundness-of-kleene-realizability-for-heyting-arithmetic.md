# Soundness of Kleene realizability for Heyting arithmetic

Every formula provable in [Heyting arithmetic](heyting-arithmetic.md) is [realizable](kleene-realizability.md). Since no number realizes $\bot$, HA is consistent, and by
[Kreisel's theorem](kreisel-s-theorem-on-provably-total-functions.md) so is Peano arithmetic.

The proof is by induction on derivations in a Hilbert-style system for HA, with a realizer for each axiom; for example $\Lambda a.\, \Lambda b.\, a$, built with the
$S^m_n$ theorem, realizes $A \to B \to A$.

## Depends on

- [Heyting arithmetic](heyting-arithmetic.md)
- [Kleene realizability](kleene-realizability.md)

## Proof depends on

- [Kreisel's theorem on provably total functions](kreisel-s-theorem-on-provably-total-functions.md)
- [Computable codes depending on a parameter](../../../TheoryOfComputation/computability/exists-computable-code.md): an index for $b \mapsto a$ computable from $a$, for the realizers of constant functions

## Expansion

This page becomes ready once:

- The cases of the induction for the remaining axioms and rules, which the lecture notes below omit, checked against Kleene, *Introduction to Metamathematics*, §82 (source check)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 11.5.2 with its proof sketch, and Corollaries 11.5.3 and 11.5.4.
