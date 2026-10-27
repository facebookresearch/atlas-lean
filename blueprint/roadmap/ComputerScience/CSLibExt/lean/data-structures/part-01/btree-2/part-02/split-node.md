---
article_id: af_989335e90fb1518145eb3da6
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.splitNode
---

# Split Node

Split an overfull internal node around its median separator: the left tree keeps the
first `t - 1` keys and first `t` children, the median key is promoted, and the right tree
keeps the remaining keys and children.

## Depends on

- [BTree](../part-01/btree.md)
- [Ins Result](../part-01/ins-result.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
