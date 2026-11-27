# Implication of inclusion dependencies is PSPACE-complete

Fix a countably infinite set of values. The problem whose input is a finite schema, a finite set $\Sigma$ of
[inclusion dependencies](../dependencies-and-the-chase/ind.md) on it and an inclusion dependency $\sigma$ on it, and which asks whether $\Sigma$
[finitely implies](../dependencies-and-the-chase/finitely-implies.md) $\sigma$ over that value domain, with [satisfaction](../dependencies-and-the-chase/inclusion-dependencies-and-finite-implication.md)
as defined there, is PSPACE-complete. Finiteness restricts the relation extents, not the supply of values, and the
value domain matters: over a one-element domain, $R[A] \subseteq R[B]$ holds in every instance, while over the
countably infinite domain the one-row relation $\{(0, 1)\}$ refutes it. For inclusion dependencies alone finite and
[unrestricted](../dependencies-and-the-chase/implies.md) implication coincide over this domain, so the same holds for unrestricted implication. Completeness means that the problem is in PSPACE and that every problem in PSPACE has a
polynomial-time many-one reduction to it.

## Expansion

This node states a precise result. Finite controllability relates the finite and unrestricted implication tests; the
PSPACE lower bound is a separate reduction from acceptance of an input word by a two-tape Turing machine that runs in
linear space (the cited textbook's Exercise 1.17). A good expansion adds a page for the PSPACE-hardness of that
acceptance problem and for the reduction, and links them under `## Proof depends on`.

## Depends on

- [Satisfaction of an inclusion dependency](../dependencies-and-the-chase/inclusion-dependencies-and-finite-implication.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)
- [Syntax of an inclusion dependency](../dependencies-and-the-chase/ind.md)
- [Finite implication of dependencies](../dependencies-and-the-chase/finitely-implies.md)
- [Unrestricted implication of dependencies](../dependencies-and-the-chase/implies.md)

## Proof depends on

- [Finite and unrestricted implication of functional and inclusion dependencies](../dependencies-and-the-chase/finite-and-unrestricted-implication-of-functional-and-inclusion.md)
- [Unrestricted implication of inclusion dependencies via the chase](../dependencies-and-the-chase/chase-for-functional-and-inclusion-dependencies/unrestricted-implication-of-inds-via-the-chase.md)
- [Implication of inclusion dependencies via compact witnesses](../dependencies-and-the-chase/chase-for-functional-and-inclusion-dependencies/implication-of-inds-via-compact-witnesses.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the countably infinite set of values (p. 9), Theorem 11.9 (p. 82), Lemma 11.10 (p. 82), Theorem 11.11 and Corollary 11.12 (p. 83), and Exercise 1.17 (p. 88).
