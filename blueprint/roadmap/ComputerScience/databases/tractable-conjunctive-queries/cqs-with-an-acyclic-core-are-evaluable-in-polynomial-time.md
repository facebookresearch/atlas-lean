# Conjunctive queries with an acyclic core are evaluable in polynomial time

A core of a conjunctive query $q(\bar x)$ is a query $q'(\bar x)$ whose atoms form a subset of those of $q$, such
that some homomorphism that is the identity on constants maps $q$ to $q'$ fixing $\bar x$ and no query on a proper
subset of the atoms of $q'$ receives such a homomorphism from $q'$; a core of $q$ is equivalent to $q$ and unique up
to renaming of variables. Constants must stay fixed: otherwise $R(a), R(b)$ with constants $a \ne b$ would have the
inequivalent core $R(a)$.

Let ACoreCQ be the class of conjunctive queries that have an acyclic core (a core whose hypergraph has a join tree).
ACoreCQ-Evaluation, the problem of deciding for $q \in$ ACoreCQ, a database $D$ and a tuple $\bar a$ whether
$\bar a \in q(D)$, is in polynomial time: for a Boolean query $q$ whose core is acyclic, $q(D)$ is true if and only if the
[$1$-consistency procedure](k-consistency-procedure.md) on $q$ and $D$ does not fail, so neither the core nor a join
tree is computed. This is the case $k = 1$ of the result for
cores of bounded generalized hypertreewidth. Some conjunctive queries are not acyclic although their core is, for
example $R(x, y), R(y, z), R(z, x), R(u, u)$, whose core is $R(u, u)$.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Minimizations and cores of conjunctive queries](../conjunctive-queries/cores-and-minimization/minimizations-and-cores-of-conjunctive-queries.md)
- [Characterizations of acyclic database schemas](../join-processing/characterizations-of-acyclic-database-schemas.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [The k-consistency procedure for Boolean conjunctive queries](k-consistency-procedure.md)

## Proof depends on

- [Generalized hypertreewidth at most one is acyclicity](generalized-hypertreewidth-one-is-acyclicity.md)
- [Conjunctive queries whose core has bounded generalized hypertreewidth](cqs-whose-core-has-bounded-ghw-are-tractable.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 16.2 (p. 124) and Corollary 16.9 (p. 129).
- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Algorithm 7 (p. 164), Propositions 19.5 and 19.6 and Theorem 19.7 (p. 165), and Exercise 3.7 (p. 246).
