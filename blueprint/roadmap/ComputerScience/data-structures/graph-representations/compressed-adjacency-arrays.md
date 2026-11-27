# Compressed adjacency arrays

The *adjacency-list interface* on vertices $[n]$ answers $\mathrm{degree}(u)$ and $\mathrm{edge}(u, i)$, the $i$-th out-edge of $u$ with its target and weight, for a fixed weighted directed multigraph; its state never changes. *Compressed adjacency arrays* store the compressed-sparse-row encoding in memory: an offsets array $\mathrm{off}[0..n]$ with $\mathrm{off}[u]$ the start of $u$'s edges and an edge array holding each edge as two cells (target, weight), so that $\mathrm{degree}(u) = \mathrm{off}[u+1] - \mathrm{off}[u]$. A degree query reads two cells and an edge query reads three, so each query costs $O(1)$ memory operations, and the representation occupies $n + 1 + 2m$ cells for $m$ edges.

## Depends on

- [Word-addressed memory as a specification](../data-structure-interfaces-and-refinement/word-addressed-memory-specification.md)
- [Compressed-sparse-row encoding of a directed graph](../../sorting-and-searching/word-ram-integer-algorithms/compressed-sparse-row-graph-encoding.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. E. Tarjan, "Data Structures and Network Algorithms", SIAM, 1983.
