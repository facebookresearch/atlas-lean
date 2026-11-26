# Implication of embedded dependencies is undecidable

A dependency (in the unirelational setting) is a first-order sentence
$\forall \bar x\,(\varphi(\bar x) \to \exists \bar z\, \psi(\bar y))$ where $\varphi$ is a conjunction of relation atoms
using all of $\bar x$, $\psi$ is a nonempty conjunction of relation and equality atoms, $\bar z$ lists the variables of
$\psi$ not in $\bar x$, and no equality atom involves a variable of $\bar z$; every such dependency is equivalent to a
set of tuple- and equality-generating dependencies. It is full when $\bar z$ is empty, and typed when its variables can
be assigned to columns so that each occurs only in its column and equalities relate variables of the same column.

For typed dependencies, and already for embedded multivalued dependencies, finite and unrestricted implication do not
coincide and both are undecidable: finite implication is not recursively enumerable and unrestricted implication is
not co-recursively enumerable.

## Expansion

This node states a precise result that the cited textbook summarizes without a full proof (it derives the untyped case
from functional and unary inclusion dependencies and refers to the literature for the typed case and for embedded
multivalued dependencies). A good expansion checks those original proofs and cites them under `## Sources`.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Inclusion dependencies and finite implication](inclusion-dependencies-and-finite-implication.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Informally uses

- [Finite and unrestricted implication of functional and inclusion dependencies](finite-and-unrestricted-implication-of-functional-and-inclusion.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Section 10.1 (pp. 217–219) and Theorem 10.1.2(2) (p. 220).
