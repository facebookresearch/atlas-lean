# Equivalence of Datalog queries is undecidable

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$.

The problem that asks, for Datalog queries $q_1$ and $q_2$ over the same extensional relation names, whether
$q_1(D) = q_2(D)$ for every database $D$, is undecidable: $q_1 \subseteq q_2$ holds if and only if $q_2$ is equivalent
to the query that returns the union of $q_1$ and $q_2$, which a Datalog program expresses with two extra rules.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Containment of Datalog queries is undecidable](containment-of-datalog-queries-is-undecidable.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.16 and Proposition 35.17 (p. 319), and Theorem 38.9 (p. 343).
