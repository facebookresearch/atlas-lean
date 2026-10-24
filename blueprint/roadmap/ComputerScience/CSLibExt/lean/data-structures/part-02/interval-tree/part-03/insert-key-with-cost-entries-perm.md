---
article_id: af_ec722b07f41f44bb85c113d9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.IntervalTree.Tree.insertKeyWithCost_entries_perm
---

# Insert Key With Cost entries perm

Insertion permutes the entry list by consing the new entry onto the
old entries with any same-key entry filtered out.

## Depends on

- [Cost](../part-01/cost.md)
- [Entry](../part-01/entry.md)
- [Key](../part-01/key.md)
- [Tree](../part-01/tree.md)
- [Key Ordered](key-ordered.md)
- [Insert Key With Cost](../part-02/insert-key-with-cost.md)

## Proof depends on

- [Mk Node](../part-01/mk-node.md)
- [Rebalance With Cost](../part-02/rebalance-with-cost.md)
- [Rotate Left](../part-02/rotate-left.md)
- [Rotate Left Right](../part-02/rotate-left-right.md)
- [Rotate Right](../part-02/rotate-right.md)
- [Rotate Right Left](../part-02/rotate-right-left.md)
- [Compare Key](../part-01/compare-key.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.IntervalTree](../../../../../../../../sources/v2/CSLibExt.md)
