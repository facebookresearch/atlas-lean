# Insertion into B+-trees preserves well-formedness

Bottom-up insert-or-replace into a well-formed B+-tree of minimum degree $t$ yields a well-formed B+-tree representing the updated map: the entry is placed in its leaf; a leaf with more than $2t - 1$ entries keeps its first $t$ entries and the rest form a new leaf whose first key is *copied* to the parent as a separator; an interior node with more than $2t - 1$ separators keeps its first $t$, *moves* the next separator up, and the following children form a new node; an overflowing root grows a new root. The operation visits one node per level and makes at most $2t$ key comparisons per visited node.

## Proof sketch

Each split produces two nodes with at least $t - 1$ items, and the copied or moved separator lies between the keys of the two halves, so the separation invariant is restored at the parent. Depths stay equal because a split adds a sibling at the same depth and only a root split increases the height, uniformly.

## Depends on

- [B+-tree of minimum degree t](b-plus-tree.md)

## Proof depends on

- [Height of a B+-tree is logarithmic](height-of-a-b-plus-tree.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. Comer, "The Ubiquitous B-Tree", ACM Computing Surveys 11(2), pp. 121-137, 1979.
