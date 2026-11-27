# Garlík: Res(k) is not automatable unless P = NP

For every integer $k \ge 2$, the $k$-DNF resolution system $\mathrm{Res}(k)$ does not have the weak feasible disjunction property. Moreover, for every $k \ge 1$, if $\mathrm{NP} \not\subseteq \mathrm{P}$ (respectively $\mathrm{QP}$, $\mathrm{SUBEXP}$) then $\mathrm{Res}(k)$ is not automatable in polynomial (respectively quasi-polynomial, subexponential) time.

## Proof sketch

Generalize the Atserias-Müller formula to $k$-DNF lines: the satisfiable case still yields short $\mathrm{Res}(k)$ refutations, and in the unsatisfiable case a switching-lemma based random restriction collapses $k$-DNF lines to short decision trees, reducing the lower bound to resolution width bounds for the relativized principle.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Proof depends on

- [Atserias–Müller: automating resolution is NP-hard](atserias-muller.md)
- [Håstad's switching lemma](../../../TheoryOfComputation/circuit-complexity/lower-bounds-for-ac0-circuits/hastad-s-switching-lemma.md)

## Sources

- M. Garlík, "Failure of feasible disjunction property for k-DNF resolution and NP-hardness of automating it", CCC (2024).
