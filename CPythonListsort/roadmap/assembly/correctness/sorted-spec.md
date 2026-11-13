---
declaration: def
origin: bridged
statement: formalized
lean: CPythonListsort.Sorted
---

# Sorted-array specification

Define `Sorted lt ys` as
`ys.toList.Pairwise (fun earlier later => lt later earlier = false)`. Prove a
small API lemma relating this form to the absence of a later element strictly
preceding an earlier element. The main artifact is the `Sorted` predicate used
by every local correctness theorem. `PendingRunsCorrect.runSorted` exports this
exact predicate—there is no pending-specific sortedness wrapper.

## Depends on

- [Total Boolean comparator model](../../transcription/comparator-model.md)

## Sources

- [Top-level theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
- [Mathlib sortedness prior art](../../../sources/mathlib-prior-art.md#sortedness-and-permutation)
