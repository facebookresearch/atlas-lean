---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.patienceStep
---

# Patience Step

One step, for `tails` sorted increasingly (the invariant that `patienceScan` keeps from `#[]`,
`PatienceInv`): replace the first entry `≥ x`, or append `x` if there is none. The position comes
from `lowerBound`, whose contract assumes a sorted array; on unsorted input it need not be the
first entry `≥ x`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lower Bound](../../search/lower-bound/lower-bound.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.PatienceSorting](../../../../../../sources/v2/CSLibExt.md)
