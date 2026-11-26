# Generalized hypertree decompositions and generalized hypertreewidth

Let $H = (V, E)$ be a hypergraph. A tree decomposition of $H$ is a pair $(T, \chi)$ of a tree $T$ and a map $\chi$
assigning a subset of $V$ to each node of $T$, such that every hyperedge $e \in E$ satisfies $e \subseteq \chi(s)$
for some node $s$, and for every $v \in V$ the nodes $s$ with $v \in \chi(s)$ form a connected subtree of $T$. A
generalized hypertree decomposition of $H$ is a triple $(T, \chi, \lambda)$ where $(T, \chi)$ is a tree decomposition
of $H$ and $\lambda$ assigns to each node $s$ a set $\lambda(s) \subseteq E$ of hyperedges with
$\chi(s) \subseteq \bigcup_{e \in \lambda(s)} e$. Its width is $\max_s \lvert \lambda(s) \rvert$, and the generalized
hypertreewidth of $H$ is the least width of a generalized hypertree decomposition of $H$.

The hypergraph $H_q$ of a conjunctive query $q$ has the variables of $q$ as vertices and, for each atom, the set of
variables occurring in it as a hyperedge. The generalized hypertreewidth of $q$ is that of $H_q$, and for $k \ge 1$,
$\mathrm{GHW}(k)$ is the class of conjunctive queries of generalized hypertreewidth at most $k$; it is strictly
contained in $\mathrm{GHW}(k+1)$.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Tree-decomposition](../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the definition of the hypergraph of a conjunctive query (p. 154), the tree decompositions of hypergraphs (p. 183), Definitions 22.1 and 22.2 and the remark that $\mathrm{GHW}(k) \subsetneq \mathrm{GHW}(k+1)$ (pp. 183–184).
