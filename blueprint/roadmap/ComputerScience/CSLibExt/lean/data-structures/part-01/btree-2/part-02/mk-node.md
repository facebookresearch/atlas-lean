---
article_id: af_3ff96d587904eed2d5054b79
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.mkNode
---

# Mk Node

The smart constructor for internal nodes after insertion below: keep the node when it
has at most `2 * t - 1` keys, and split it otherwise.

## Depends on

- [BTree](../part-01/btree.md)
- [Ins Result](../part-01/ins-result.md)

## Proof depends on

- [Split Node](split-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
