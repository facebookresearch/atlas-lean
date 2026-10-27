---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.maxSubarraySum_ret_eq_some_iff
---

# Max Subarray Sum ret eq some iff

Kadane's algorithm returns a value exactly when the input is nonempty, and that value is the
maximum sum of a nonempty contiguous run.

## Depends on

- [Is Max Subarray Sum](is-max-subarray-sum.md)
- [Max Subarray Sum](max-subarray-sum.md)

## Proof depends on

- [Ne nil](ne-nil.md)
- [Unique](unique.md)
- [Is Max Suffix Sum](is-max-suffix-sum.md)
- [Kadane Scan](kadane-scan.md)
- [Kadane Scan ret](kadane-scan-ret.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray](../../../../../../sources/v2/CSLibExt.md)
