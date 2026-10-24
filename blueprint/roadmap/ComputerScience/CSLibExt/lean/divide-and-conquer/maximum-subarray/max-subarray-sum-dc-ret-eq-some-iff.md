---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.maxSubarraySumDC_ret_eq_some_iff
---

# Max Subarray Sum DC ret eq some iff

The divide-and-conquer algorithm returns a value exactly when the input is nonempty, and that
value is the maximum sum of a nonempty contiguous run.

## Depends on

- [Is Max Subarray Sum](../../dynamic-programming/maximum-subarray/is-max-subarray-sum.md)
- [Max Subarray Sum DC](max-subarray-sum-dc.md)

## Proof depends on

- [Is Max Prefix Sum](is-max-prefix-sum.md)
- [Append](append.md)
- [Ne nil](../../dynamic-programming/maximum-subarray/ne-nil.md)
- [Unique](../../dynamic-programming/maximum-subarray/unique.md)
- [Is Max Suffix Sum](../../dynamic-programming/maximum-subarray/is-max-suffix-sum.md)
- [Max Subarray DC](max-subarray-dc.md)
- [Prefix Scan](prefix-scan.md)
- [Suffix Scan](suffix-scan.md)
- [Suffix Scan spec](suffix-scan-spec.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DivideAndConquer.MaximumSubarray](../../../../../../sources/v2/CSLibExt.md)
