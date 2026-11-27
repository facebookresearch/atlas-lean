# Inhabitation for simple types is PSPACE-complete

The inhabitation problem for [simple type assignment](simple-type-assignment-a-la-curry.md), whether a given simple type has a closed inhabitant, is
PSPACE-complete (Statman). Reading each type variable as a propositional variable and each arrow as implication, and conversely, translates types and
implicational formulas into each other in linear time, preserving the syntax tree; by the Curry–Howard correspondence a type has a closed inhabitant exactly
when the corresponding formula is provable in intuitionistic implicational logic. So provability in that logic is PSPACE-complete as well.

Membership in PSPACE comes from an alternating polynomial-time search for a long normal inhabitant; hardness from a reduction of the validity of
quantified Boolean formulas.

## Depends on

- [Simple type assignment à la Curry](simple-type-assignment-a-la-curry.md)
- [Polynomial space for decision problems](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)
- [Polynomial-time many-one reduction](../../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)
- [Curry–Howard correspondence for implicational logic](../../curry-howard-correspondence-for-implicational-logic.md)

## Proof depends on

- [TQBF is PSPACE-complete](../../../../TheoryOfComputation/completeness-other-classes/true-quantified-boolean-formulas/tqbf-pspace-complete.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Proposition 6.0.12 (equivalence with intuitionistic implicational logic), Section 6.6, Lemma 6.6.1 (alternating polynomial-time algorithm), Lemma 6.6.2 and Theorem 6.6.3 (PSPACE-completeness).
