# Bulk loading of B+-trees and B-trees from sorted lists

For every $t \ge 2$ and every strictly increasing list of $N$ key-value pairs, bottom-up bulk loading (cutting the list into leaves of between $t - 1$ and $2t - 1$ entries and grouping consecutive nodes into parents of between $t$ and $2t$ children) produces a well-formed B+-tree whose leaves concatenate to the input list (a list of at most $2t - 1$ entries forms a single root leaf, and the topmost group of between $2$ and $2t$ nodes forms the root). The analogous construction for classic B-trees produces a well-formed B-tree of minimum degree $t$ whose inorder flattening is the input list.

## Proof sketch

Any $N \ge t - 1$ items can be split into consecutive groups of sizes between $t - 1$ and $2t - 1$ (balance the last two groups), and likewise any number of at least $t$ nodes into groups of between $t$ and $2t$; applying this level by level, with the separators taken from the least keys of the right groups, terminates at a single root.

## Depends on

- [B+-tree of minimum degree t](b-plus-tree.md)
- [B-trees of a given minimum degree](../b-tree/is-btree.md)

## Sources

- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), pp. 121-137, 1979.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. Ramakrishnan and J. Gehrke, "Database Management Systems", 3rd edition, McGraw-Hill, 2003 (Chapter 10, bulk-loading a B+ tree).
