# Datalog evaluation is PTIME-complete in data complexity

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ whose rule heads contain only variables, each
occurring in the rule body (the cited source's Definition 35.1), and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$.

Datalog evaluation is PTIME-complete in data complexity: for every fixed Datalog query $q$, deciding for a database $D$
and a tuple $\bar a$ whether $\bar a \in q(D)$ takes time $O((1 + \lvert \mathrm{Dom}(D) \rvert)^k)$ for some $k$ depending
only on $q$; and for some fixed Datalog query this problem is PTIME-hard, by a reduction from the monotone circuit
value problem.

## Expansion

This node states a precise result. A good expansion adds a page for the P-completeness of the monotone circuit value
problem under log-space reductions, from which the cited proof reduces, and links it under `## Proof depends on`;
P-completeness of the general circuit value problem does not by itself give hardness for monotone circuits.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [Log-space many-one reductions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Related topics

- [The Circuit Value Problem is P-complete](../../../TheoryOfComputation/completeness-other-classes/circuit-value-problem/cvp-p-complete.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.1 (p. 319), Definition 35.16 and Proposition 35.17 (p. 327), and Theorem 37.2 with its proof (p. 342).
