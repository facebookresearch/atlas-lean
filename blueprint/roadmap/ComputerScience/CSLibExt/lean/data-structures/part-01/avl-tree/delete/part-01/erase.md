---
article_id: af_ae92e9f9b5310531b7e80bfa
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.AvlTree.erase
---

# Erase

Delete a key, rebalancing every node on the search path. A deleted node with
two children takes the minimum key of its right subtree as its new key and
deletes that minimum with `eraseMin`.

## Depends on

- [Tree](../../../avl-tree-2/part-01/tree.md)

## Proof depends on

- [Balance](../../../avl-tree-2/part-01/balance.md)
- [Delete Min](delete-min.md)
- [Min D](min-d.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.AvlTree.Delete](../../../../../../../../../sources/v2/CSLibExt.md)
