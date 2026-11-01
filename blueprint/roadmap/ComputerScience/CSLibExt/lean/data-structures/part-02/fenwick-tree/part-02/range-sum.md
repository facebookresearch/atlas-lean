---
article_id: af_3ed54c561004c975dbc00b98
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.rangeSum
---

# Range Sum

The sum of the underlying entries with indices in `[lo, hi)`, as a
difference of prefix sums. This is the one operation that needs additive
inverses. Reversed or empty ranges (`hi ≤ lo`) return `0`, matching the sum
over the empty list interval `((arr.take hi).drop lo)`.

## Depends on

- [Fenwick Tree](../part-01/fenwick-tree.md)

## Proof depends on

- [Prefix Sum](../part-01/prefix-sum.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
