---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.NoEscape
---

# No Escape

No escape from `z` avoiding `U` and `D`: no alternating chain from `z` of shortest length
(`m + 1` pairs when `z` is first reached in round `m + 1`) whose left vertices are not in `U` and
whose right vertices after `z` are not in `D`. A phase gives this property to every right vertex
it marks dead after a failed search (`searchPath_dead`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exact Level](exact-level.md)
- [Is Chain From](is-chain-from.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
