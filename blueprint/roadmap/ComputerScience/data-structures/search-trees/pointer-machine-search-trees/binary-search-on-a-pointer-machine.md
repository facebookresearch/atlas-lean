# Binary search on a pointer machine

A fixed pointer-machine program, given a linked binary search tree and a query key, returns the record holding the key (or null) by following left and right links, using only strict key comparison as a scalar primitive and modifying no record. Its instruction count is $O(h + 1)$, where $h$ is the height of the tree. Applied to a linked AVL tree on $n$ keys, search takes $O(\log n)$ pointer-machine instructions.

## Proof sketch

Each loop iteration compares the query with one node's key, tests the chosen child for null and follows it, a constant number of instructions per level; the number of iterations is at most the height. For AVL trees the height is logarithmic.

## Depends on

- [Linked representation of a binary search tree](linked-representation-of-search-trees.md)
- [Search in a binary search tree](../binary-search-tree/contains.md)

## Proof depends on

- [Logarithmic height bound for AVL trees](../avl-tree/avl-height-and-operation-counts/height-le-log2.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
- R. E. Tarjan, "A Class of Algorithms Which Require Nonlinear Time to Maintain Disjoint Sets", Journal of Computer and System Sciences 18(2), 1979.
