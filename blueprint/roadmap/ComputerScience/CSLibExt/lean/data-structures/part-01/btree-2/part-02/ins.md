---
article_id: af_7e76a50d393fe778d0abf8ba
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.ins
---

# Ins

Split-returning insertion into a subtree. The auxiliary `insList` walks the separator
and child lists of an internal node from the left, descends into the unique child whose
separator range contains the key, and rebuilds the lists on the way back, inserting the
extra child and promoted median when that child split. The rebuilt node is then passed
through `mkNode`.

## Depends on

- [BTree](../part-01/btree.md)
- [Ins Result](../part-01/ins-result.md)

## Proof depends on

- [Ins Leaf](../part-01/ins-leaf.md)
- [Mk Node](mk-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
