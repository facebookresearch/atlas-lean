# Node-visit costs of unbalanced search-tree operations

In an unbalanced binary search tree, search, insertion, minimum and successor each visit only the nodes of one root-to-node path selected by key comparisons, so their number of visited internal nodes is at most the height of the tree, with no balancing assumption; insertion increases the height by at most one. Hence $n$ insertions in sorted order produce a path and cost $\Theta(n^2)$ node visits in total.

## Proof sketch

Each operation descends one child per comparison and never explores both subtrees. A new key becomes a leaf below an existing node, adding at most one level. Inserting $1, 2, \dots, n$ in order makes each new key the right child of the previous one.

## Depends on

- [Ordered binary trees](../binary-search-tree/ordered.md)
- [Insertion into a binary search tree](../binary-search-tree/insert.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
