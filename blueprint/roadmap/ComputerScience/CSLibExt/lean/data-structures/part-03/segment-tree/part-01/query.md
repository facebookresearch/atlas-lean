---
article_id: af_39d136e0ab73d977c0089adb
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SegmentTree.query
---

# Query

The range aggregate over `[l, r)`, with indices relative to the tree's segment.

An empty range and a node disjoint from the range on either side contribute
`0` without descending, a fully covered node contributes its cached aggregate,
and otherwise the query recurses into both children.

## Depends on

- [Segment Tree](segment-tree.md)

## Proof depends on

- [Size](size.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SegmentTree](../../../../../../../../sources/v2/CSLibExt.md)
