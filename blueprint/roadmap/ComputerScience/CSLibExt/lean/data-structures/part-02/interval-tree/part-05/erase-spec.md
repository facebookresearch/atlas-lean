---
article_id: af_18ae5e7d03fec9c97fe7f780
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.IntervalTree.IndexedIntervalTree.erase_spec
---

# Erase spec

Public erasure preserves the bundled invariant and deletes exactly
the occurrence with the given identifier; absent identifiers leave the
stored entries unchanged.

## Depends on

- [Cost](../part-01/cost.md)
- [Entry](../part-01/entry.md)
- [Indexed Interval Tree](../part-04/indexed-interval-tree.md)
- [Invariant](../part-04/invariant.md)
- [Erase With Cost](../part-04/erase-with-cost.md)
- [Tree](../part-01/tree.md)

## Proof depends on

- [Key](../part-01/key.md)
- [Interval](../part-01/interval.md)
- [Balanced Prop](../part-02/balanced-prop.md)
- [Cache Invariant](../part-01/cache-invariant.md)
- [Key Ordered](../part-03/key-ordered.md)
- [Valid Invariant](../part-01/valid-invariant.md)
- [Balanced Prop erase Key With Cost](../part-03/balanced-prop-erase-key-with-cost.md)
- [Cache Invariant erase Key With Cost](../part-04/cache-invariant-erase-key-with-cost.md)
- [Erase Key With Cost](../part-02/erase-key-with-cost.md)
- [Erase Key With Cost entries perm](../part-03/erase-key-with-cost-entries-perm.md)
- [Key Nodup of key Ordered](../part-03/key-nodup-of-key-ordered.md)
- [Key Ordered erase Key With Cost](../part-03/key-ordered-erase-key-with-cost.md)
- [Mk Node](../part-01/mk-node.md)
- [Rebalance With Cost](../part-02/rebalance-with-cost.md)
- [Remove Min With Cost](../part-02/remove-min-with-cost.md)
- [Rotate Left](../part-02/rotate-left.md)
- [Rotate Left Right](../part-02/rotate-left-right.md)
- [Rotate Right](../part-02/rotate-right.md)
- [Rotate Right Left](../part-02/rotate-right-left.md)
- [Valid Invariant erase Key With Cost](../part-04/valid-invariant-erase-key-with-cost.md)
- [Compare Key](../part-01/compare-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.IntervalTree](../../../../../../../../sources/v2/CSLibExt.md)
