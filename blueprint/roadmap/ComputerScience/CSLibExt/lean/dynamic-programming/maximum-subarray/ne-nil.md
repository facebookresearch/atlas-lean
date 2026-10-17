---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.IsMaxSubarraySum.ne_nil
---

# Ne nil

Kadane's scan performs exactly three operations per element after the first. -/
@[simp]
theorem maxSubarraySum_time (xs : List α) :
    (maxSubarraySum xs).time = 3 * (xs.length - 1) := by
  cases xs with
  | nil => simp [maxSubarraySum]
  | cons x xs => simp [maxSubarraySum]

/-! ## The specification

## Depends on

- [Is Max Subarray Sum](is-max-subarray-sum.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray](../../../../../../sources/v2/CSLibExt.md)
