# Implication of full dependencies is decidable

A dependency (in the unirelational setting) is a first-order sentence
$\forall \bar x\,(\varphi(\bar x) \to \exists \bar z\, \psi(\bar y))$ where $\varphi$ is a conjunction of relation atoms
using all of $\bar x$, $\psi$ is a nonempty conjunction of relation and equality atoms, $\bar z$ lists the variables of
$\psi$ not in $\bar x$, and no equality atom involves a variable of $\bar z$; every such dependency is equivalent to a
set of tuple- and equality-generating dependencies. It is full when $\bar z$ is empty, and typed when its variables can
be assigned to columns so that each occurs only in its column and equalities relate variables of the same column.

For sets of full dependencies, finite and unrestricted implication coincide, and implication is decidable: a set
$\Sigma$ of full dependencies implies a dependency $\tau$ if and only if chasing $\tau$ by $\Sigma$, which always
terminates with a unique result, yields a trivial dependency.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Inclusion dependencies and finite implication](inclusion-dependencies-and-finite-implication.md)

## Informally uses

- [Finite and unrestricted implication of functional and inclusion dependencies](finite-and-unrestricted-implication-of-functional-and-inclusion.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Section 10.1 (pp. 217–219), Theorem 10.1.2(1) (p. 220), Theorems 10.2.1 and 10.2.2 (pp. 220–221).
