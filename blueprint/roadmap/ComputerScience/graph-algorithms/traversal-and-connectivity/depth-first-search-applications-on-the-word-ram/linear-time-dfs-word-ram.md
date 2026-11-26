# Topological sort and Kosaraju SCC in O(n + m) word-RAM time

There are deterministic word-RAM programs that, given a directed graph with $n$ vertices and $m$ arcs in compressed sparse row form, (i) compute the decreasing DFS finishing order with an explicit stack in $O(n + m)$ instructions, (ii) build the transpose graph in compressed sparse row form in $O(n + m)$ instructions, (iii) output a topological order or report a cycle in $O(n + m)$ instructions, and (iv) output the strongly connected components with their condensation indices in $O(n + m)$ instructions, at every word size with $n + m < 2^{w}$ up to a constant factor.

## Depends on

- [Compressed-sparse-row encoding of a directed graph](../../../sorting-and-searching/word-ram-integer-algorithms/compressed-sparse-row-graph-encoding.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Reverse DFS finishing order is a topological order exactly for acyclic graphs](dfs-topological-sort.md)
- [Kosaraju's algorithm computes the strongly connected components in condensation order](kosaraju-scc-correctness.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
- R. E. Tarjan, "Depth-First Search and Linear Graph Algorithms", SIAM Journal on Computing 1(2), 1972.
