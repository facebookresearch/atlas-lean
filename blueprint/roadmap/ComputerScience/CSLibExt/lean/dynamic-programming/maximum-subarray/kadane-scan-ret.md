---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.kadaneScan_ret
---

# Kadane Scan ret

The scan invariant: if the accumulators are the best run ending at the end of the read
prefix and the best run in it, the scan returns the maximum subarray sum of the whole list.

## Depends on

- [Is Max Subarray Sum](is-max-subarray-sum.md)
- [Is Max Suffix Sum](is-max-suffix-sum.md)
- [Kadane Scan](kadane-scan.md)

## Proof depends on

- [Concat](concat-2.md)
- [Concat](concat.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray](../../../../../../sources/v2/CSLibExt.md)
