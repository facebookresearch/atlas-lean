# Direct-address table

A *direct-address table* for keys $[U]$ is an array of $U$ cells, cell $u$ holding the encoding of $s(u) \in \{\bot\} \cup \mathbb{N}$ ($0$ for absent, $v + 1$ for value $v$). It implements the dynamic dictionary with every query, insertion and deletion in one memory read or write and $U$ cells of space, and zeroed memory represents the empty dictionary; it is optimal in time but uses $U$ cells regardless of the number of stored keys.

## Depends on

- [Bounded-capacity dictionary specification](bounded-capacity-dictionary.md)
- [Word-addressed memory as a specification](../../../data-structure-interfaces-and-refinement/word-addressed-memory-specification.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
