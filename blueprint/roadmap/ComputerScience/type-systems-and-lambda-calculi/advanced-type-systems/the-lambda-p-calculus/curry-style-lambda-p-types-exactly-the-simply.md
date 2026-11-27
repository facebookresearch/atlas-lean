# Curry-style λP types exactly the simply typable terms

For a pure λ-term $N$ write $\Gamma \vdash_P N : \tau$ if $N = |M|$ for some term $M$ of [λP](the-calculus-lambda-p.md) with $\Gamma \vdash M : \tau$, where $|\cdot|$ erases the
type annotations of abstractions. Then:

1. a pure term is typable in this Curry-style λP if and only if it is typable in [simple type assignment](../../simply-typed-lambda-calculus/decision-problems-for-simple-types/simple-type-assignment-a-la-curry.md);
2. consequently type reconstruction for Curry-style λP is decidable in polynomial time.

For the first part, the dependency erasure of a λP typing $\Gamma \vdash M : \tau$ is a simply typed typing $\overline{\Gamma} \vdash \overline{M} : \overline{\tau}$ of a term with the same
erasure $|\overline{M}| = |M|$; the converse holds because simple types are λP types.

## Depends on

- [The calculus λP](the-calculus-lambda-p.md)
- [Simple type assignment à la Curry](../../simply-typed-lambda-calculus/decision-problems-for-simple-types/simple-type-assignment-a-la-curry.md)

## Proof depends on

- [Type reconstruction for simple types is P-complete](../../simply-typed-lambda-calculus/decision-problems-for-simple-types/type-reconstruction-for-simple-types-is-p.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definition 10.4.1, Definition 10.4.3, Lemma 10.4.4 and Proposition 10.4.5.
