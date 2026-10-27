---
article_id: af_a0f8bc55ecdee2c05805a8f9
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.cut
---

# Cut

Detach the subtree rooted at `x` from its represented tree (the rooted
`cut`): the result contains the detached subtree itself, rooted at `x`,
and the remainder of the old tree with that subtree pruned off
(`pruneAt`), keeping every remaining edge. When `x` is the root of its
tree the remainder is empty and only the detached tree remains. Preferred
edges are reset.

## Depends on

- [State](../part-03/state.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Find Subtree](../part-01/find-subtree.md)
- [Find Tree](../part-01/find-tree.md)
- [Prune At](../part-02/prune-at.md)
- [Remove Tree](../part-01/remove-tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
