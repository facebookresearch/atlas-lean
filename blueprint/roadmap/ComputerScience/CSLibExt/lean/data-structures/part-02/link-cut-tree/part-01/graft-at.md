---
article_id: af_b32d2dd181de37abaf2ebe16
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.graftAt
---

# Graft At

Attach `newChild` as a new last child of the node labelled `y`, keeping
every existing node and edge. Returns `none` when `y` does not occur. This
is the tree surgery behind `State.link`: it adds exactly the edge from `y`
to the root of `newChild`.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
