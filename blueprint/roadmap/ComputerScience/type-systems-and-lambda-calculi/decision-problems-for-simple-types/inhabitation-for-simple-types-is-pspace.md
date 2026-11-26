# Inhabitation for simple types is PSPACE-complete

The inhabitation problem for [simple type assignment](simple-type-assignment-a-la-curry.md), whether a given simple type has a closed inhabitant, is
PSPACE-complete (Statman). Through the Curry–Howard correspondence it is recursively equivalent to provability in the implicational fragment of
intuitionistic propositional logic, which is therefore PSPACE-complete as well.

Membership in PSPACE comes from an alternating polynomial-time search for a long normal inhabitant; hardness from a reduction of the validity of
quantified Boolean formulas.

## Depends on

- [Simple type assignment à la Curry](simple-type-assignment-a-la-curry.md)

## Proof depends on

- [TQBF is PSPACE-complete](../../../TheoryOfComputation/completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md)
- [Curry–Howard correspondence for implicational logic](../curry-howard-correspondence-for-implicational-logic.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Proposition 6.0.12 (equivalence with intuitionistic implicational logic), Lemma 6.6.1 (alternating polynomial-time algorithm), Lemma 6.6.2 and Theorem 6.6.3 (PSPACE-completeness).
