# Consistency criterion for Boolean acyclic conjunctive queries

Let $q = \mathrm{Answer} \mathrel{:-} R_1(\bar u_1), \dots, R_n(\bar u_n)$ be a Boolean acyclic conjunctive query, $D$ a database,
and $q_i$ the conjunctive query with the single atom $R_i(\bar u_i)$ whose output tuple is $\bar u_i$ without its constants. Then
$q(D)$ is true if and only if there are nonempty sets $S_1 \subseteq q_1(D), \dots, S_n \subseteq q_n(D)$ that are pairwise
consistent: $S_i = S_i \ltimes S_j$ for all $i, j \in [n]$. Consequently the procedure that starts from $S_i = q_i(D)$,
replaces $S_i$ by $S_i \ltimes S_j$ while some $S_i \ne S_i \ltimes S_j$, and then fails if some $S_i$ is empty, succeeds
exactly when $q(D)$ is true. It is the $1$-consistency procedure of
[the k-consistency procedure for Boolean conjunctive queries](../k-consistency-procedure.md).

## Depends on

- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Characterizations of acyclic database schemas](../../join-processing/characterizations-of-acyclic-database-schemas.md)

## Proof depends on

- [Semijoin recurrence along a join tree for Boolean acyclic queries](semijoin-recurrence-along-a-join-tree.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 19.4, Algorithm 7 and Proposition 19.5 (pp. 163–165), the latter proved in Exercise 3.6.
