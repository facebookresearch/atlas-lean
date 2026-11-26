# Conjunctive queries with an acyclic core are evaluable in polynomial time

A core of a conjunctive query $q(\bar x)$ is a query $q'(\bar x)$ whose atoms form a subset of those of $q$, such
that some homomorphism maps $q$ to $q'$ fixing $\bar x$ and no query on a proper subset of the atoms of $q'$ receives
such a homomorphism from $q'$; a core of $q$ is equivalent to $q$ and unique up to renaming of variables.

Let ACoreCQ be the class of conjunctive queries that have an acyclic core (a core whose hypergraph has a join tree).
ACoreCQ-Evaluation, the problem of deciding for $q \in$ ACoreCQ, a database $D$ and a tuple $\bar a$ whether
$\bar a \in q(D)$, is in polynomial time; the consistency (semijoin) procedure that decides Boolean acyclic queries
also decides Boolean queries whose core is acyclic, without computing the core. Some conjunctive queries are not
acyclic although their core is.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [CQ minimization (cores) and UCQ containment](../conjunctive-queries/cq-minimization-and-ucq-containment.md)
- [Characterizations of acyclic database schemas](../join-processing/characterizations-of-acyclic-database-schemas.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Yannakakis' algorithm for acyclic join queries](../join-processing/yannakakis-algorithm-for-acyclic-join-queries.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 16.2 (p. 124) and Corollary 16.9 (p. 129).
- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Propositions 19.5 and 19.6 and Theorem 19.7 (p. 165), and Exercise 3.7 (p. 238).
