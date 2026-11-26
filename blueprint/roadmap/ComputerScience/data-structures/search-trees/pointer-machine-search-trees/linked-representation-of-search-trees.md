# Linked representation of a binary search tree

A *linked representation* of a binary tree on a pointer machine maps each node to a record with left and right pointer fields, a key field, payload fields and optionally a cached height, such that the record of a node points to the records of its children (null for empty children), distinct nodes have distinct records, and the root is designated by a pointer. A *context* of a subtree is the sequence of ancestor records with the direction taken at each, which allows a modified subtree to be reconnected to its parent.

## Depends on

- [Pointer machine](pointer-machine.md)
- [Ordered binary trees](../binary-search-tree/ordered.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
- R. E. Tarjan, "A Class of Algorithms Which Require Nonlinear Time to Maintain Disjoint Sets", Journal of Computer and System Sciences 18(2), 1979.
