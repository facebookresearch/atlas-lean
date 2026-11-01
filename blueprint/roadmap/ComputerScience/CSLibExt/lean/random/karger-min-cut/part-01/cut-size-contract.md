---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Karger.cutSize_contract
---

# Cut Size contract

Every cut of the contracted multigraph is a cut of the original of the same size: `Y` on the
contraction counts the same edges as `Y ∘ rename` on the original.

## Depends on

- [State](state.md)
- [Contract](contract.md)
- [Cut Size](cut-size.md)
- [Rename](rename.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Random.KargerMinCut](../../../../../../../sources/v2/CSLibExt.md)
