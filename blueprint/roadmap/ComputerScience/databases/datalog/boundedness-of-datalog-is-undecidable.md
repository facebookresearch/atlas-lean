# Boundedness of Datalog programs and queries is undecidable

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ whose rule heads contain only variables, each
occurring in the rule body (the cited source's Definition 35.1), and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$. For a Datalog program $\Pi$, a database $D$ and an intensional relation name $R$, the stage of $R$ is the least
$k$ such that $R$ has the same content after $k$ applications of the immediate-consequence operator to $D$ as in
$\Pi(D)$; the stage of $\Pi$ on $D$ is the least $k$ at which the whole iteration stabilizes. The query $(\Pi, R)$ is
bounded if the stage of $R$ is at most a fixed $k$ on every database, and the program $\Pi$ is bounded if its stage is
at most a fixed $k$ on every database.

It is undecidable whether a given Datalog program is bounded, and undecidable whether a given Datalog query is bounded.
Boundedness of programs remains undecidable for constant-free programs, for programs with a single recursive rule, and
for programs with a single intensional relation name.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.1 (p. 319), Definition 35.16 and Proposition 35.17 (p. 327), Definitions 38.11 and 38.13 (pp. 352–353) and Theorem 38.15 (p. 355).
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Theorem 12.5.7 and the remarks following it (p. 304).
