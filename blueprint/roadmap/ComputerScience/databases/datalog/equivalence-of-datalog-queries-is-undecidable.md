# Equivalence of Datalog queries is undecidable

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ whose rule heads contain only variables, each
occurring in the rule body (the cited source's Definition 35.1), and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$.

The problem that asks, for Datalog queries $q_1 = (\Pi_1, R_1)$ and $q_2 = (\Pi_2, R_2)$ over the same extensional
relation names and with output relations of the same arity, whether $q_1(D) = q_2(D)$ for every database $D$, is
undecidable. Rename the intensional relation names of $\Pi_1$ and $\Pi_2$ apart and add a fresh relation name $T$ with
the rules $T(\bar x) \mathrel{:-} R_1(\bar x)$ and $T(\bar x) \mathrel{:-} R_2(\bar x)$; then $q_1 \subseteq q_2$ holds if and
only if the resulting query with output $T$ is equivalent to $q_2$.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Containment of Datalog queries is undecidable](containment-of-datalog-queries-is-undecidable.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.1 (p. 319), Definition 35.16 and Proposition 35.17 (p. 327), and Theorem 38.9 (p. 351).
