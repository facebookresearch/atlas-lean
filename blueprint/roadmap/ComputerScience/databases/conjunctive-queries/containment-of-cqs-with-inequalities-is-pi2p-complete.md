# Containment of conjunctive queries with inequalities is Π2p-complete

The decision problem that asks, for two conjunctive queries with inequalities $q$ and $q'$, whether $q \subseteq q'$ is
$\Pi_2^p$-complete: it lies in $\Pi_2^p$, and every problem in $\Pi_2^p$ has a polynomial-time many-one reduction to it.
Non-containment is decided in $\Sigma_2^p$ by guessing $h \in H_{q,q'}$ and checking with an NP oracle that
no homomorphism maps $q'$ to $h(q^+)$, with $H_{q,q'}$ and $h(q^+)$ as in the
[homomorphism criterion for containment of conjunctive queries with inequalities](containment-of-cqs-with-inequalities-via-homomorphic-images.md). Equivalence of such queries is $\Pi_2^p$-complete as well.

## Expansion

This node states a precise result. The cited source proves the upper bound and leaves the lower bound to its Exercise
4.4. A good expansion adds a page for a checked reduction from the validity of quantified Boolean formulas
$\forall \bar x\, \exists \bar y\, \psi$ (the complement of $\mathrm{QSAT}_2$) to containment of conjunctive queries with
inequalities, and links it under `## Proof depends on`.

## Depends on

- [Conjunctive queries with inequalities](conjunctive-queries-with-inequalities.md)
- [The universal levels of the polynomial hierarchy](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pi-k.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [Homomorphism criterion for containment of conjunctive queries with inequalities](containment-of-cqs-with-inequalities-via-homomorphic-images.md)
- [$\mathrm{QSAT}_k$ is $\Sigma_k^p$-complete, uniformly in $k$](../../../TheoryOfComputation/completeness-other-classes/quantified-boolean-formulas-with-bounded-alterna/qsat-k-sigma-k-complete.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 30.10 (p. 278) and Theorem 30.12 (p. 279).
