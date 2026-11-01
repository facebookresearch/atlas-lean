---
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.PatienceInv
---

# Patience Inv

After processing the prefix `P`, the tails `t` are strictly increasing, entry `k` is the last
element of some strictly increasing subsequence of `P` of length `k + 1`, and every strictly
increasing subsequence of `P` ending at `y` has length at most `t.length`, with
`t[length - 1] ≤ y`.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.PatienceSorting](../../../../../../sources/v2/CSLibExt.md)
