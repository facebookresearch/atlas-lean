---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.maxSubarraySumDC_time_le
---

# Max Subarray Sum DC time le

On a nonempty list of length `n` the divide-and-conquer algorithm uses at most
`2 * n * ⌈log₂ n⌉ + 3 * (n - 1)` operations (stated with the `3` moved left).

## Depends on

- [Max Subarray Sum DC](max-subarray-sum-dc.md)

## Proof depends on

- [Max Subarray DC](max-subarray-dc.md)
- [Max Subarray DCCost](max-subarray-dccost.md)
- [Prefix Scan](prefix-scan.md)
- [Suffix Scan](suffix-scan.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DivideAndConquer.MaximumSubarray](../../../../../../sources/v2/CSLibExt.md)
