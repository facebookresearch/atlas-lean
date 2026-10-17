---
article_id: af_ca3421e96dc312886b79256f
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.merge
---

# Merge

Merge two trees of the same height and a separator key between them
into a single node: the keys concatenate around the separator and the
children concatenate. Used when both trees hold `t - 1` keys, so the
result holds `2 * t - 1`.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
