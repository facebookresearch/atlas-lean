# Deletion from B+-trees preserves well-formedness

Erasing a key (and removing the least or greatest entry) from a well-formed B+-tree of minimum degree $t$ yields a well-formed B+-tree representing the updated map. An underfull leaf or node is repaired by borrowing from an adjacent sibling through their common separator when the sibling has more than $t - 1$ items, and otherwise by merging with that sibling and removing the separator from the parent; a root left with a single child is replaced by that child.

## Proof sketch

Borrowing keeps both siblings within bounds and updates the separator to the new least key of the right sibling; merging two nodes with $t - 2$ and $t - 1$ items yields at most $2t - 2$ items. The parent loses one separator per merge, which may cascade upward, and the root shrinks only when it has one child, preserving equal leaf depths.

## Depends on

- [B+-tree of minimum degree t](b-plus-tree.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), pp. 121-137, 1979.
- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
