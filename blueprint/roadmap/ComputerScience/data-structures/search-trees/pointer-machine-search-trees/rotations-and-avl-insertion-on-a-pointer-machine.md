# Height-maintaining rotations and AVL insertion on a pointer machine

Single and double subtree rotations, which preserve the inorder sequence of keys, are performed on linked search trees by a constant number of pointer-machine instructions, updating the cached heights of the rotated nodes and reconnecting the subtree to its parent via its context. Consequently AVL insertion, which descends with a parent cursor, attaches a fresh leaf (one allocation), and rebalances along the path back to the root, is realized by a pointer-machine program with $O(\log n)$ instructions on trees with $n$ keys, preserving all payload fields other than heights. Compiling this program to the word RAM gives AVL insertion with a logarithmic instruction count and at most one node allocated.

## Proof sketch

A rotation rewires three child pointers and recomputes two cached heights, each from its children's cached heights. AVL insertion performs at most one single or double rotation at the lowest unbalanced ancestor and constant work at each ancestor, and the height is logarithmic.

## Depends on

- [Linked representation of a binary search tree](linked-representation-of-search-trees.md)
- [Insertion into an AVL tree](../avl-tree/insert.md)

## Proof depends on

- [Binary search on a pointer machine](binary-search-on-a-pointer-machine.md)
- [Logarithmic height bound for AVL trees](../avl-tree/avl-height-and-operation-counts/height-le-log2.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
