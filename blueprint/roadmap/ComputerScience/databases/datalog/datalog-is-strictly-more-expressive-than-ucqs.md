# Datalog queries are strictly more expressive than unions of conjunctive queries

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ whose rule heads contain only variables, each
occurring in the rule body (the cited source's Definition 35.1), and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$.

Every union of conjunctive queries $q_1 \cup \cdots \cup q_n$ with head tuple $\bar x$ is equivalent to the Datalog
query whose program consists of the rules $\mathrm{Answer}(\bar x) \mathrel{:-} \mathrm{body}(q_i)$, so Datalog queries
express all unions of conjunctive queries. The converse fails: the reachability query on directed graphs, given by the
program $T(x, y) \mathrel{:-} E(x, y)$ and $T(x, y) \mathrel{:-} E(x, z), T(z, y)$ with output $T$, is not expressible
by any union of conjunctive queries.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Informally uses

- [Connectivity is not first-order definable on finite graphs](../query-language-expressiveness/connectivity-is-not-first-order-definable-on-finite-graphs.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.1 (p. 319), Definition 35.16 and Proposition 35.17 (p. 327), and Theorem 35.18 (p. 327).
