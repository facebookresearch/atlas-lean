---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.maxAbove_time
---

# Max Above time

A longest strictly increasing subsequence, by the quadratic dynamic program. -/
def longestIncreasingSubsequence (xs : List α) : TimeM ℕ (List α) := do
  let t ← lisTable xs
  let b ← maxEntry t
  pure b.2

/-! ## Cost

## Depends on

- [Max Above](max-above.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.LongestIncreasingSubsequence](../../../../../../sources/v2/CSLibExt.md)
