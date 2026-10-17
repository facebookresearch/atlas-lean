---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.tryPreds_isSome
---

# Try Preds is Some

`tryPreds` finds a path when some candidate passes `ok` and every such candidate is unmatched
or has a partner from which `search` succeeds with the initial dead set (the dead set does not
change until the first candidate that passes `ok`).

## Depends on

- [Try Preds](try-preds.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
