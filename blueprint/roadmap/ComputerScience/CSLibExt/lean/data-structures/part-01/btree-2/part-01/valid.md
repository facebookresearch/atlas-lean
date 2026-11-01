---
article_id: af_511c1f0fd01947b32688dd64
declaration: inductive
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.Valid
---

# Valid

The structural invariant of a B-tree of minimum degree `t`, indexed by the minimum key
count `mink` required at the top node and by the height `height`. A leaf has height `0`;
an internal node has height one more than its children, and since every child is required
to have the same height, all leaves of a valid tree sit at the same depth. Every node has
at most `2 * t - 1` keys, the top node has at least `mink` keys, every other node has at
least `t - 1` keys, and an internal node with `k` keys has exactly `k + 1` children.
Non-root trees are used with `mink = t - 1`; the root invariant is `ValidRoot`.

## Depends on

- [BTree](btree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
