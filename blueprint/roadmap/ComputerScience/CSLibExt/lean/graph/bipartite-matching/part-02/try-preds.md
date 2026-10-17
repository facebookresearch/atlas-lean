---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.tryPreds
---

# Try Preds

Try the candidate predecessors `is` of `j` in order: for the first `i` with `ok i`, if `i` is
unmatched the path is `[(i, j)]`, otherwise continue from its partner with `search`; a failed
search leaves its dead vertices marked for the next candidate. If every candidate fails, `j` is
marked dead too.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Mark Dead](mark-dead.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
