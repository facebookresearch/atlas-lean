---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.kadaneScan_time
---

# Kadane Scan time

Kadane's algorithm: the maximum sum of a nonempty contiguous run, or `none` for the empty
list. The first element seeds both accumulators. -/
def maxSubarraySum : List α → TimeM ℕ (Option α)
  | [] => pure none
  | x :: xs => some <$> kadaneScan x x xs

/-! ## Cost

## Depends on

- [Kadane Scan](kadane-scan.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray](../../../../../../sources/v2/CSLibExt.md)
