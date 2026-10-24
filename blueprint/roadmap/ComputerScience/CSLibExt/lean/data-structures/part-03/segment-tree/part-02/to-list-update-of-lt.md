---
article_id: af_0d76004c0dfe8c06ed248270
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SegmentTree.toList_update_of_lt
---

# To List update of lt

Point update at an in-range index of a valid tree updates the leaf list at
that index. Validity is what ties the cached sizes used for routing to the
leaf list.

## Depends on

- [Segment Tree](../part-01/segment-tree.md)
- [Valid](../part-01/valid.md)
- [Size](../part-01/size.md)
- [To List](../part-01/to-list.md)
- [Update](../part-01/update.md)

## Proof depends on

- [Agg](../part-01/agg.md)
- [Length to List of valid](../part-01/length-to-list-of-valid.md)
- [To List node](../part-01/to-list-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SegmentTree](../../../../../../../../sources/v2/CSLibExt.md)
