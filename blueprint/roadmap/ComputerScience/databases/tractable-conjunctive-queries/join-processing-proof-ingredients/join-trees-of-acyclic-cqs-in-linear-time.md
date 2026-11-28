# Join trees of acyclic conjunctive queries can be computed in linear time

A conjunctive query is acyclic when its hypergraph, with the variables as vertices and the variable sets of the atoms as
hyperedges, has a [join tree](../../join-processing/has-join-tree.md). There is an algorithm that, given a
conjunctive query $q$, decides in time $O(\|q\|)$ whether $q$ is acyclic and, if it is, constructs a join tree of its hypergraph.

## Depends on

- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Characterizations of acyclic database schemas](../../join-processing/characterizations-of-acyclic-database-schemas.md)
- [Join tree](../../join-processing/has-join-tree.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definitions 18.1, 18.2 and 18.4 and Proposition 18.8 (pp. 152–157).
- R. E. Tarjan and M. Yannakakis, "Simple linear-time algorithms to test chordality of graphs, test acyclicity of hypergraphs, and selectively reduce acyclic hypergraphs", *SIAM J. Comput.* 13(3) (1984) 566–579, as credited there.
