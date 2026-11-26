# Treewidth of a conjunctive query

For a conjunctive query $q = \mathrm{Answer}(\bar x) \mathrel{:-} R_1(\bar u_1), \dots, R_n(\bar u_n)$, the Gaifman
graph $G_q$ is the undirected graph whose vertices are the variables that occur in some $\bar u_i$ and do not occur
in the head tuple $\bar x$, with an edge between two distinct such variables when they occur together in some
$\bar u_i$. The treewidth $\mathrm{tw}(q)$ of $q$ is the treewidth of $G_q$, and for $k \ge 1$, $\mathrm{TW}(k)$ is
the class of conjunctive queries of treewidth at most $k$.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Tree-width at most $k$](../../../GraphTheory/planar-graphs-and-minors/tree-width/has-treewidth-at-most.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the definition of the Gaifman graph of a conjunctive query (pp. 179–180) and Definition 21.9 (p. 180).
