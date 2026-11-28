# Polynomial data complexity of stratified Datalog with negation

[Stratified Datalog with negation](stratified-datalog-with-negation.md) states stratifiability, stratum-by-stratum
evaluation and the independence of the result from the stratification. This node states the complexity clause.

For every fixed stratifiable Datalog program $P$ with negation, the stratified semantics of $P$ on an input instance
$I$ over its extensional predicates is computable in time polynomial in the size of $I$: each stratum is evaluated by
naive iteration to its least fixed point over the active domain of $I$ and the constants of $P$, which takes
polynomially many rounds, each of polynomial cost. The bound is in data complexity; no polynomial bound is claimed
when the program is part of the input.

## Depends on

- [Stratified Datalog with negation](stratified-datalog-with-negation.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Theorem 15.2.10 and the remark after its proof that the stratified semantics is computable in time polynomial in the input (p. 383). <http://webdam.inria.fr/Alice/pdfs/all.pdf>
