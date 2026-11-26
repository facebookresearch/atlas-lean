# The stratified semantics is a minimal model

Let $P$ be a stratifiable $\mathrm{datalog}^\neg$ program and $I$ an instance over its extensional relations, and let
$P^{\mathrm{strat}}(I)$ be its stratified semantics, computed stratum by stratum with each stratum evaluated as a
semipositive program. Then

1. $P^{\mathrm{strat}}(I)$ is a minimal model of $P$ whose restriction to the extensional relations equals $I$; and
2. $P^{\mathrm{strat}}(I)$ is a minimal fixpoint of $T_P$ whose restriction to the extensional relations equals $I$.

It need not be the only minimal model: a $\mathrm{datalog}^\neg$ program can have several.

## Depends on

- [Stratifications and the precedence graph of a Datalog program with negation](stratifications-and-the-precedence-graph.md)
- [Stratified Datalog with negation](../stratified-datalog-with-negation.md)

## Proof depends on

- [Semipositive Datalog programs have a least model](semipositive-datalog-programs-have-a-least-model.md)
- [Models of a Datalog program are the pre-fixpoints of its immediate consequence operator](../fixpoint-semantics/models-of-a-datalog-program-are-pre-fixpoints-of-tp.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Proposition 15.2.11 (p. 383).
