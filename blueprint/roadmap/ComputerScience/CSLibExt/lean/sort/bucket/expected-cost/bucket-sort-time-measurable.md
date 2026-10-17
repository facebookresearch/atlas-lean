---
article_id: af_ff00e5985aee6b221ba0be5d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.bucketSort_time_measurable
---

# Bucket Sort time measurable

The actual conditional saved-bucket executor time is measurable, with no caller premise.

## Depends on

- [Bucket Sort](../basic/bucket-sort.md)

## Proof depends on

- [Bucket Sort empty](../basic/bucket-sort-empty.md)
- [Bucket Sort time](../basic/bucket-sort-time.md)
- [Compare LE](../../insertion-cost/compare-le.md)
- [Insertion Sort](../../insertion-cost/insertion-sort.md)
- [Insertion Sort eq insertion Sort M](../../insertion-cost/insertion-sort-eq-insertion-sort-m.md)
- [Insertion Sort perm](../../insertion-cost/insertion-sort-perm.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Sort.Bucket.ExpectedCost](../../../../../../../sources/v2/CSLibExt.md)
