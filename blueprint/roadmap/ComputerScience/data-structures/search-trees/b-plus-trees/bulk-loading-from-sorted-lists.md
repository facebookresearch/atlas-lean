# Bulk loading of B+-trees and B-trees from sorted lists

For every $t \ge 2$ and every strictly increasing list of $N$ key-value pairs, bottom-up bulk loading (cutting the list into leaves of between $t - 1$ and $2t - 1$ entries and grouping consecutive nodes into parents of between $t$ and $2t$ children) produces a well-formed B+-tree whose leaves concatenate to the input list. The analogous construction for classic B-trees produces a well-formed B-tree of minimum degree $t$ whose inorder flattening is the input list.

## Proof sketch

Any $N \ge t - 1$ items can be split into consecutive groups of sizes between $t - 1$ and $2t - 1$ (balance the last two groups), and the same splitting applies at each level to the list of nodes, terminating at a single root.

## Depends on

- [B+-tree of minimum degree t](b-plus-tree.md)
- [B-trees of a given minimum degree](../b-tree/is-btree.md)

## Sources

- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), 1979.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
