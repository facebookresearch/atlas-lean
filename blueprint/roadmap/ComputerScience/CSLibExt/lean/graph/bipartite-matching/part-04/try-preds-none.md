---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.tryPreds_none
---

# Try Preds none

When `tryPreds` fails, `j` is marked dead and every candidate passing `ok` has a partner whose
search failed with a dead set contained in the final one.

## Depends on

- [Try Preds](../part-02/try-preds.md)

## Proof depends on

- [Try Preds mono](../part-02/try-preds-mono.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
