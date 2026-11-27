# Semijoin recurrence along a join tree for Boolean acyclic queries

Let $q$ be a Boolean acyclic conjunctive query with atoms $R_1(\bar u_1), \dots, R_n(\bar u_n)$, let $T$ be a rooted
[join tree](../../join-processing/characterizations-of-acyclic-database-schemas.md) of its hypergraph, whose nodes are the variable sets $X_i$ of the
atoms, and let $D$ be a database. For a node $s$ let $q_s$ be the conjunctive query with the single atom of $s$ whose output
tuple lists its variables, and let $Q_s$ be the conjunctive query with all atoms in the subtree of $T$ rooted at $s$ and output
the variables of $s$. Then

- if $s$ is a leaf, $Q_s(D) = q_s(D)$; and
- if $s$ has children $s_1, \dots, s_p$, then $Q_s(D) = q_s(D) \ltimes Q_{s_1}(D) \ltimes \dots \ltimes Q_{s_p}(D)$, iterating semijoins.

Hence $q(D)$ is true if and only if $Q_r(D) \ne \emptyset$ for the root $r$, which a bottom-up pass of semijoins computes.

## Depends on

- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Characterizations of acyclic database schemas](../../join-processing/characterizations-of-acyclic-database-schemas.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 19.2 and Algorithm 6 (pp. 161–162).
