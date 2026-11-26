# Conjunctive queries whose core has bounded generalized hypertreewidth

A core of a conjunctive query $q(\bar x)$ is a query $q'(\bar x)$ whose atoms form a subset of those of $q$, such
that some homomorphism maps $q$ to $q'$ fixing $\bar x$ and no query on a proper subset of the atoms of $q'$ receives
such a homomorphism from $q'$; a core of $q$ is equivalent to $q$ and unique up to renaming of variables.

Fix $k \ge 1$. The evaluation problem for the class of conjunctive queries whose core has generalized hypertreewidth
at most $k$ is solvable in polynomial time: for a Boolean such query $q$ and a database $D$, $q(D)$ is true if and
only if the $k$-consistency procedure on $q$ and $D$ does not fail.

## Depends on

- [Generalized hypertree decompositions and generalized hypertreewidth](generalized-hypertree-decompositions-and-width.md)
- [Minimizations and cores of conjunctive queries](../conjunctive-queries/cores-and-minimization/minimizations-and-cores-of-conjunctive-queries.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Conjunctive queries of bounded generalized hypertreewidth are evaluable in polynomial time](bounded-ghw-cqs-are-evaluable-in-polynomial-time.md)
- [Conjunctive queries with an acyclic core are evaluable in polynomial time](cqs-with-an-acyclic-core-are-evaluable-in-polynomial-time.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 16.2 (p. 124) and Corollary 16.9 (p. 129).
- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 22.7 and Theorem 22.8 (pp. 187–188).
