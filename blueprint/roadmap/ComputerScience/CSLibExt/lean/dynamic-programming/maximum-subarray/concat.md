---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.IsMaxSuffixSum.concat
---

# Concat

Appending `x` updates the best run ending at the last element to `max x (e + x)`: either the
run is `[x]` alone, or it extends a best run ending just before `x`.

## Depends on

- [Is Max Suffix Sum](is-max-suffix-sum.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray](../../../../../../sources/v2/CSLibExt.md)
