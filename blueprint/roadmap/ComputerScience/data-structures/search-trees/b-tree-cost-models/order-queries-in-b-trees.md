# Order queries in classic B-trees

On a well-formed classic B-tree with sorted entries, the least and greatest entry, the strict predecessor and strict successor of a key, the rank of a key (the number of stored keys below it), and the closed-interval range query $[\ell, h]$ (returning the entries with keys in $[\ell, h]$ in increasing order) are correct with respect to the sorted inorder flattening of the tree. Minimum, maximum, predecessor and successor visit $O(h)$ nodes, rank visits $O(h)$ nodes when every node records the entry counts of its children's subtrees (otherwise it must also count the subtrees to the left of its path), and the range query visits $O(h + k)$ nodes, where $h$ is the height and $k$ the output size.

## Proof sketch

Predecessor and successor descend one path, keeping the best separator seen as a candidate; rank adds the sizes of the subtrees and keys to the left of the path. The range query visits the two boundary paths and all subtrees strictly between them, each of which contributes at least one output entry per visited node.

## Depends on

- [B-trees of a given minimum degree](../b-tree/is-btree.md)

## Proof depends on

- [Size–height inequalities for classic B-trees](size-height-inequalities-for-b-trees.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- R. Bayer and E. M. McCreight, "Organization and Maintenance of Large Ordered Indexes", Acta Informatica 1(3), pp. 173-189, 1972.
- D. E. Knuth, "The Art of Computer Programming, Volume 3: Sorting and Searching", 2nd edition, Addison-Wesley, 1998.
