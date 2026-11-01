---
article_id: af_8270a05c0aed4f0156e86561
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.IntervalTree.IndexedIntervalTree.search_sound
---

# Search sound

Public search soundness.  This holds for every indexed tree: the
bundled invariant is not needed, only the successful search equation.

## Depends on

- [Cost](../part-01/cost.md)
- [Entry](../part-01/entry.md)
- [Indexed Interval Tree](../part-04/indexed-interval-tree.md)
- [Interval](../part-01/interval.md)
- [Overlaps](../part-01/overlaps.md)
- [Valid](../part-01/valid-2.md)
- [Tree](../part-01/tree.md)
- [Search With Cost](../part-02/search-with-cost.md)

## Proof depends on

- [Overlaps](../part-01/overlaps-2.md)
- [Overlaps With Cost](../part-01/overlaps-with-cost.md)
- [Overlaps With Cost fst](../part-01/overlaps-with-cost-fst.md)
- [Cached Max?](../part-01/cached-max.md)
- [Search](../part-02/search.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.IntervalTree](../../../../../../../../sources/v2/CSLibExt.md)
