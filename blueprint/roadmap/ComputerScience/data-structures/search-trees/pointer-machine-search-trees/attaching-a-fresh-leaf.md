# Attaching a fresh leaf in a linked search tree

Given a linked binary search tree, a query key absent from the tree, and the parent cursor and comparison path produced by a parent-preserving search, a pointer-machine program allocates one record for the key, writes its fields, and stores its pointer into the empty child slot reached by the search, in a constant number of instructions. The result is a linked representation of the binary search tree obtained by unbalanced insertion; all other records are unchanged, and the context of the new leaf is the search path.

## Proof sketch

The parent-preserving search ends at the parent whose child in the comparison direction is null; the insertion position of an absent key in a binary search tree is exactly that slot.

## Depends on

- [Linked representation of a binary search tree](linked-representation-of-search-trees.md)
- [Insertion into a binary search tree](../binary-search-tree/insert.md)

## Proof depends on

- [Binary search on a pointer machine](binary-search-on-a-pointer-machine.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
