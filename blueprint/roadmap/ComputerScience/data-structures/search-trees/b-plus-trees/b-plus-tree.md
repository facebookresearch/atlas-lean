# B+-tree of minimum degree t

A *B+-tree* of minimum degree $t \ge 2$ stores a finite map from a linearly ordered key set to values with every entry in a leaf. An interior node holds a first child followed by a list of (separator, child) pairs, so a node with $m$ separators has $m + 1$ children; the keys in the child introduced by separator $s$ are at least $s$, and the keys of every earlier child are strictly below $s$ (a separator need not be a stored key). The tree is *well formed* if keys are sorted, all leaves have the same depth, every non-root leaf holds between $t - 1$ and $2t - 1$ entries, every non-root interior node has between $t - 1$ and $2t - 1$ separators, and the root holds at most $2t - 1$ entries or separators (at least one separator if it is interior). Concatenating the leaves from left to right lists the map in key order.

## Depends on

- [B-trees of a given minimum degree](../b-tree/is-btree.md)

## Sources

- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), pp. 121-137, 1979.
- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
