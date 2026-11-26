# Datalog evaluation is PTIME-complete in data complexity

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$.

Datalog evaluation is PTIME-complete in data complexity: for every fixed Datalog query $q$, deciding for a database $D$
and a tuple $\bar a$ whether $\bar a \in q(D)$ takes time $O(\lvert \mathrm{Dom}(D) \rvert^k)$ for some $k$ depending
only on $q$; and for some fixed Datalog query this problem is PTIME-hard, by a reduction from the monotone circuit
value problem.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [Log-space many-one reductions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Informally uses

- [The Circuit Value Problem is P-complete](../../../TheoryOfComputation/completeness-other-classes/circuit-value-problem/cvp-p-complete.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.16 and Proposition 35.17 (p. 319), and Theorem 37.2 with its proof (p. 334).
