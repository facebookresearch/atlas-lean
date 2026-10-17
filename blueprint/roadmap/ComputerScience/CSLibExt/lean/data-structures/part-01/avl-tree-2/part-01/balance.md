---
article_id: af_96ea1314116a180d853c9267
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.AvlTree.balance
---

# Balance

Rebuild a node from children whose heights differ by at most two, restoring the
balance invariant. When the left child is too tall, a single right rotation is
performed if the left-left grandchild is at least as tall as the left-right one,
and a double left-right rotation otherwise; the right-heavy case is symmetric.
Children that already differ by at most one are rebuilt with `mkNode`.

## Depends on

- [Tree](tree.md)

## Proof depends on

- [Height](height.md)
- [Mk Node](mk-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.AvlTree](../../../../../../../../sources/v2/CSLibExt.md)
