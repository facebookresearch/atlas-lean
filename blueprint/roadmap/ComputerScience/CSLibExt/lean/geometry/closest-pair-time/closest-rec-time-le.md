---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.closestRec_time_le
---

# Closest Rec time le

On `n` points sorted by `x`, the recursion computes at most `7 n ⌈log₂ n⌉ + n` distances.

## Depends on

- [Closest Rec](../closest-pair/closest-rec.md)

## Proof depends on

- [In Strip](in-strip.md)
- [Is Answer](../closest-pair/is-answer.md)
- [Same Side Far](same-side-far.md)
- [Tagged](tagged.md)
- [Brute Min](../closest-pair/brute-min.md)
- [Brute Min time](../closest-pair/brute-min-time.md)
- [Closest Rec is Answer](../closest-pair/closest-rec-is-answer.md)
- [Dist2](../closest-pair/dist2.md)
- [Strip Scan](../closest-pair/strip-scan.md)
- [Strip Scan time le](strip-scan-time-le.md)
- [Omin](../../data-structures/part-03/sparse-table/omin.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ClosestPairTime](../../../../../../sources/v2/CSLibExt.md)
