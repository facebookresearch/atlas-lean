---
article_id: af_eb3ea4bd6d147daed7a425dc
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RodCutting.extendedBottomUpCutRod
---

# Extended Bottom Up Cut Rod

Save all optimal revenues and the first maximizing cut at each positive length.
The source's `r[j]` is the revenue vector's entry `j`; `s[j]` is the cut vector's
entry `j - 1`. Ascending candidates update only on strict improvement.
One event is charged per candidate, including the first candidate of each row.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.RodCutting](../../../../../../../sources/v2/CSLibExt.md)
