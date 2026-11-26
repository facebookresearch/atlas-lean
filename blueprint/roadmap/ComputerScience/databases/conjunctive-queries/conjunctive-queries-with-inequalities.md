# Conjunctive queries with inequalities

A conjunctive query with inequalities ($\mathrm{CQ}^{\ne}$) over a schema is a query
$\mathrm{Answer}(\bar x) \mathrel{:-} R_1(\bar u_1), \dots, R_n(\bar u_n), v_1 \ne v'_1, \dots, v_m \ne v'_m$ with
$n \ge 1$ and $m \ge 0$, where the relational part is a conjunctive query, each $v_i$ is a variable occurring in some
$\bar u_k$, and each $v'_i$ is a variable occurring in some $\bar u_k$ or a constant. On a database $D$ its answer set is
the set of tuples $\eta(\bar x)$ over all assignments $\eta$ from its variables to $\mathrm{Dom}(D)$, extended to
constants as the identity, that map every relational atom to a fact of $D$ and satisfy
$\eta(v_i) \ne \eta(v'_i)$ for every $i$. A union of such queries with a common head tuple
($\mathrm{UCQ}^{\ne}$) returns the union of their answer sets. Containment $q \subseteq q'$ means
$q(D) \subseteq q'(D)$ for every database $D$.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 30.1 and 30.2 (pp. 272–273) and Definition 30.13 (p. 279).
