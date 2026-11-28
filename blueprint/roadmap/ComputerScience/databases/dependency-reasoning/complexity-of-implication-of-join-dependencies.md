# Complexity of implication of join dependencies

A join dependency $\bowtie[X_1, \dots, X_n]$ over $U$, with $X_1 \cup \cdots \cup X_n = U$, holds in a relation $I$
over $U$ when $I$ equals the join of its projections on $X_1, \dots, X_n$. Deciding, for a join dependency $\sigma$,
a functional dependency $\varphi$ and a join dependency $\tau$, whether $\{\sigma, \varphi\}$ implies $\tau$ is
NP-complete. Deciding whether a set of multivalued dependencies implies a join dependency is NP-hard.

## Expansion

This node states a precise result that the cited textbook states without proof. A good expansion checks the original
proofs credited in that book's bibliographic notes for Chapter 8 and cites them under `## Sources`.

## Depends on

- [Join dependencies and multivalued dependencies](../dependencies-and-the-chase/multivalued-and-join-dependencies/join-dependencies-and-multivalued-dependencies.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)
- [Functional dependency](../functional-dependencies/fd.md)
- [A functional dependency holds in a relation](../functional-dependencies/holds-in.md)

## Proof depends on

- [Chasing tableau queries with functional and join dependencies](../dependencies-and-the-chase/chasing-tableau-queries-with-functional-and-join-dependencie.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Definition 8.3.1 (p. 170) and Theorem 8.4.13 (p. 182).
