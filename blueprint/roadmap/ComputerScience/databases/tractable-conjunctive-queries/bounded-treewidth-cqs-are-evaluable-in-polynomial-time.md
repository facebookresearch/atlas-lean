# Conjunctive queries of bounded treewidth are evaluable in polynomial time

Fix $k \ge 1$. $\mathrm{TW}(k)$-Evaluation, the problem of deciding, for a conjunctive query $q(\bar x)$ of treewidth
at most $k$, a database $D$ and a tuple $\bar a$, whether $\bar a \in q(D)$, can be solved in time
$O\big(\lVert D \rVert^{k+1} \cdot (\lVert q \rVert + \lVert \bar a \rVert)^4 \cdot (\log \lVert D \rVert + \log \lVert q \rVert + \log \lVert \bar a \rVert)\big)$.

## Expansion

This node states a precise result. The input is a query, a database and a tuple, not a decomposition; the cited proof
first constructs a tree decomposition of the query of width at most $k$, in time $O(\lVert q \rVert^2)$ for fixed $k$
(the source's Proposition 21.10). A good expansion adds a page for that construction and links it under
`## Proof depends on`.

## Depends on

- [Treewidth of a conjunctive query](treewidth-of-a-conjunctive-query.md)

## Proof depends on

- [Tree-decomposition](../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)
- [Yannakakis' algorithm for acyclic join queries](../join-processing/yannakakis-algorithm-for-acyclic-join-queries.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 21.10 and Theorem 21.11 (p. 180).
