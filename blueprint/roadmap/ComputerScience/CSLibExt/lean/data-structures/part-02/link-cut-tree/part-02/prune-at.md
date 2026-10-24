---
article_id: af_8114e2b3420866320c2e956e
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.pruneAt
---

# Prune At

Remove every subtree rooted at `x`, keeping every other node and edge:
the original tree with the `x` subtrees pruned off. Returns `none` exactly
when the root itself is `x` (nothing remains). This is the tree surgery
behind the remainder side of `State.cut`.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
