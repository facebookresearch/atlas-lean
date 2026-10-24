---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.weightedGreedySetCover
---

# Weighted Greedy Set Cover

Weighted greedy set cover of `U` from the family `F` with costs `w`: take a set meeting `U`
with the least cost per newly covered element, remove it from `U`, repeat; stop when no set meets
`U`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Best Ratio Set](best-ratio-set.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.WeightedSetCover](../../../../../../sources/v2/CSLibExt.md)
