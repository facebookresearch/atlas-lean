---
article_id: af_98afae1e7520bf32b855da87
declaration: inductive
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.ValidRoot
---

# Valid Root

The structural invariant at the root of a B-tree of minimum degree `t` and height
`height`: a root leaf holds at most `2 * t - 1` keys (possibly none, for the empty tree),
and a root internal node holds between `1` and `2 * t - 1` keys, with every child a
non-root valid tree of the same height.

## Depends on

- [BTree](btree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
