---
article_id: af_66f4b8f39f5f6baa9ff2c29e
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.IntervalTree.IndexedIntervalTree.Invariant
---

# Invariant

Bundled representation invariant for the public indexed tree: exact
caches, strict composite-key BST ordering, stored-interval validity, AVL
balance, unique identifiers, and two-way identifier-index correspondence.
Low-endpoint ordering used by search is derived from the strict key
ordering via `Tree.keyOrdered_lowOrdered`.

## Depends on

- [Indexed Interval Tree](indexed-interval-tree.md)

## Proof depends on

- [Entry](../part-01/entry.md)
- [Interval](../part-01/interval.md)
- [Tree](../part-01/tree.md)
- [Balanced Prop](../part-02/balanced-prop.md)
- [Cache Invariant](../part-01/cache-invariant.md)
- [Key Ordered](../part-03/key-ordered.md)
- [Valid Invariant](../part-01/valid-invariant.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.IntervalTree](../../../../../../../../sources/v2/CSLibExt.md)
