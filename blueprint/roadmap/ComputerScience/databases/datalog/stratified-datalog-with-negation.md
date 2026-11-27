# Stratified Datalog with negation

A Datalog program with negation is stratifiable if and only if its precedence graph has no cycle containing
a negative edge. Given a stratification, the program is evaluated stratum by stratum, each stratum as a
Datalog program in which negated predicates from lower strata are treated as fixed input. All
stratifications of a stratifiable program yield the same result.

## Depends on

- [Stratifications and the precedence graph of a Datalog program with negation](stratified-negation/stratifications-and-the-precedence-graph.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)
- [Semipositive Datalog programs have a least model](stratified-negation/semipositive-datalog-programs-have-a-least-model.md)
- [Strata respect paths of the precedence graph](stratified-negation/strata-respect-paths-of-the-precedence-graph.md)
- [The condensation of the computed components is acyclic](../../graph-algorithms/traversal-and-connectivity/strongly-connected-components/components-condensation-acyclic.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), Proposition 15.2.7 and Theorem 15.2.10. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
