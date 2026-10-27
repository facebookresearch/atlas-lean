---
article_id: af_abeef5acef2e4e1ba7018643
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.AvlTree.le_height_eraseMin
---

# Le height erase Min

Removing the minimum shrinks the height of a balanced tree by at most one.

## Depends on

- [Balanced](../../../avl-tree-2/part-01/balanced.md)
- [Cache Correct](../../../avl-tree-2/part-01/cache-correct.md)
- [Tree](../../../avl-tree-2/part-01/tree.md)
- [Erase Min](erase-min.md)
- [Height](../../../avl-tree-2/part-01/height.md)

## Proof depends on

- [Balance](../../../avl-tree-2/part-01/balance.md)
- [Balance eq mk Node of le](../../../avl-tree-2/part-02/balance-eq-mk-node-of-le.md)
- [Cache Correct erase Min](cache-correct-erase-min.md)
- [Height erase Min le](height-erase-min-le.md)
- [Le height balance](../../../avl-tree-2/part-02/le-height-balance.md)
- [Mk Node](../../../avl-tree-2/part-01/mk-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.AvlTree.Delete](../../../../../../../../../sources/v2/CSLibExt.md)
