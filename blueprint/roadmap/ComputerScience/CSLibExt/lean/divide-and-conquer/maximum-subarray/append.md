---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.IsMaxSubarraySum.append
---

# Append

Combining the halves: a best run of `L ++ R` is a best run of `L`, a best run of `R`, or a
best suffix of `L` followed by a best prefix of `R`.

## Depends on

- [Is Max Prefix Sum](is-max-prefix-sum.md)
- [Is Max Subarray Sum](../../dynamic-programming/maximum-subarray/is-max-subarray-sum.md)
- [Is Max Suffix Sum](../../dynamic-programming/maximum-subarray/is-max-suffix-sum.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DivideAndConquer.MaximumSubarray](../../../../../../sources/v2/CSLibExt.md)
