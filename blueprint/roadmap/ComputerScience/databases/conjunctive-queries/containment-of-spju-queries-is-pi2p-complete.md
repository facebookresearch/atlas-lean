# Containment of SPJU queries is Π2p-complete

The decision problem that asks, for two SPJU queries $e$ and $e'$ (relational algebra expressions built from relation
names with selection by equality conditions, projection, product, renaming and union), whether $e(D) \subseteq e'(D)$
on every database $D$ is $\Pi_2^p$-complete, and so is equivalence of SPJU queries. Containment of unions of
conjunctive queries is in NP, so the higher bound comes from the succinctness of nested unions, whose expansion into a
union of conjunctive queries can be exponentially large. Hardness reduces from the truth of quantified Boolean
formulas $\forall \bar x\, \exists \bar y\, \psi$; the truth of $\forall \bar x\, \exists \bar y\, \psi$ is $\Pi_2^p$-hard because, for well-formed inputs, it holds
exactly when the $\mathrm{QSAT}_2$ instance $\exists \bar x\, \forall \bar y\, \neg\psi$ is false, and $\mathrm{QSAT}_2$ is
$\Sigma_2^p$-complete.

## Depends on

- [Relational algebra queries](../relational-algebra/expr.md)
- [The universal levels of the polynomial hierarchy](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pi-k.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [Containment of an SPJ query in an SPJU query is in NP](containment-of-an-spj-query-in-an-spju-query-is-in-np.md)
- [$\mathrm{QSAT}_k$ is $\Sigma_k^p$-complete, uniformly in $k$](../../../TheoryOfComputation/completeness-other-classes/quantified-boolean-formulas-with-bounded-alterna/qsat-k-sigma-k-complete.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 29.2 (p. 262), Theorem 29.6 (p. 264) and Corollary 29.7 (p. 265).
