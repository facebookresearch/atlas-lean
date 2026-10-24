---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.ErdosProblem358IntervalSumsWanted.RepCount
---

# Rep Count

Number of interval representations of `n` as a consecutive sum of `A`.

The sequence is indexed from `0` rather than the source's `1`-based
`a_1 < a_2 < ...`; this shift is harmless since only the ordered values
and interval sums matter.

`Nat.card` of a set is junk-but-total: it returns `0` when the solution
set is infinite. Finiteness gap (not formalized): for a strictly
increasing sequence of positive integers the solution set is in fact
finite, so `RepCount` agrees with the true count on all admissible
inputs.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ErdosProblem358IntervalSumsWanted](../../../../../sources/v2/WantedExt.md)
