---
article_id: af_6fb77ae1c4037124b96c7375
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.Ordered
---

# Ordered

The ordering invariant of a B-tree: the flattening is strictly increasing. This single
condition packages sortedness of the keys at each node and the separator bounds between a
node's keys and the keys stored in its subtrees; see `Ordered.node_keys_pairwise` and
`Ordered.separator_bounds`.

## Depends on

- [BTree](btree.md)

## Proof depends on

- [Flatten](flatten.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
