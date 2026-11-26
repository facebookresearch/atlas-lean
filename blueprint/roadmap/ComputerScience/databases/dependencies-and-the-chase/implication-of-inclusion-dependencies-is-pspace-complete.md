# Implication of inclusion dependencies is PSPACE-complete

For [inclusion dependencies](ind.md) on a finite schema, with [satisfaction](inclusion-dependencies-and-finite-implication.md)
and [finite implication](finitely-implies.md) as defined there, the problem of deciding, for a finite set $\Sigma$ of
inclusion dependencies and an inclusion dependency $\sigma$, whether $\Sigma$ finitely implies $\sigma$ is PSPACE-complete;
for inclusion dependencies alone finite and unrestricted implication coincide, so the same holds for unrestricted
implication. Completeness means that the problem is in PSPACE and that every problem in PSPACE has a
polynomial-time many-one reduction to it.

## Expansion

This node states a precise result. Finite controllability relates the finite and unrestricted implication tests; the
PSPACE lower bound is a separate reduction from acceptance of an input word by a two-tape Turing machine that runs in
linear space (the cited textbook's Exercise 1.17). A good expansion adds a page for the PSPACE-completeness of that
acceptance problem and for the reduction, and links them under `## Proof depends on`.

## Depends on

- [Satisfaction of an inclusion dependency](inclusion-dependencies-and-finite-implication.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)
- [Syntax of an inclusion dependency](ind.md)
- [Finite implication of dependencies](finitely-implies.md)

## Proof depends on

- [Finite and unrestricted implication of functional and inclusion dependencies](finite-and-unrestricted-implication-of-functional-and-inclusion.md)
- [Unrestricted implication of inclusion dependencies via the chase](chase-for-functional-and-inclusion-dependencies/unrestricted-implication-of-inds-via-the-chase.md)
- [Implication of inclusion dependencies via compact witnesses](chase-for-functional-and-inclusion-dependencies/implication-of-inds-via-compact-witnesses.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 11.9 (p. 82), Lemma 11.10 (p. 82), Theorem 11.11 and Corollary 11.12 (p. 83), and Exercise 1.17 (p. 88).
