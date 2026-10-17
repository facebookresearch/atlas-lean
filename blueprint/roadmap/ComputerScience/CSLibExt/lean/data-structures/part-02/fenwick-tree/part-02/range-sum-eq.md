---
article_id: af_c4d84ca6d4f0583c147f8637
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.rangeSum_eq
---

# Range Sum eq

`rangeSum` agrees with the sum of the represented array over `[lo, hi)`,
with both ends clamped through `List.take`. This holds for every `lo` and
`hi`: when `hi ≤ lo` both sides are `0`.

## Depends on

- [Fenwick Tree](../part-01/fenwick-tree.md)
- [Valid](../part-01/valid.md)
- [Range Sum](range-sum.md)

## Proof depends on

- [Prefix Sum](../part-01/prefix-sum.md)
- [Prefix Sum eq take sum](../part-01/prefix-sum-eq-take-sum.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
