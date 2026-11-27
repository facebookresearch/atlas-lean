# Proactive top-down splitting in B-tree insertion

In a B-tree of minimum degree $t$, *proactive* insertion first splits a full root (one with $2t - 1$ keys) into two nodes of $t - 1$ keys under a new root, and then, while descending, splits every full child before entering it, moving its median key into the current node, which is not full. Each split takes $O(t)$ work, the descent never needs to return upward, and the result is a well-formed B-tree whose flattening is the sorted insertion of the new entry.

## Proof sketch

The invariant that the current node is not full guarantees room for the median moved up by a child split. Splitting a full node of $2t - 1$ keys gives two nodes of $t - 1$ keys each, which satisfies the occupancy bounds, and leaf depths change only when the root splits.

## Depends on

- [B-trees of a given minimum degree](../b-tree/is-btree.md)
- [B-tree insertion](../b-tree/insert.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
