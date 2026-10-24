---
article_id: af_fa40e87f1c784dc249ea628d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.Ordered.separator_bounds
---

# Separator bounds

The separator bounds of an ordered node, in index-free form. If the key list is
`keys₁ ++ key :: keys₂` and the child list splits as `children₁ ++ children₂` with
`children₁` holding one more child than `keys₁` has keys (so the last child of `children₁`
is the subtree immediately left of `key` and the first child of `children₂` the one
immediately right of it), then every key stored on the left is below `key` and every key
stored on the right is above `key`. In particular, every key in the `i`-th child lies
strictly between the `(i-1)`-st and `i`-th separators.

## Depends on

- [BTree](btree.md)
- [Ordered](ordered.md)
- [Flatten](flatten.md)

## Proof depends on

- [Flatten node append cons](flatten-node-append-cons.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
