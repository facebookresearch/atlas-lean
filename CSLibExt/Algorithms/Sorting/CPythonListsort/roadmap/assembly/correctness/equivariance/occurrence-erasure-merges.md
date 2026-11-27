---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.eraseOccurrenceMergeHi
---

# Merge evaluators ignore occurrence origins

The forward and backward merge machines commute exactly with structural
occurrence erasure.  Their public result maps retain return codes and fuel
flags while erasing every occurrence-bearing state component
(`Correctness/OccurrenceErasureMerges.lean:249` and `:1197`;
definitions).

For a state whose stored comparator is `occurrenceComparator lt`, the public
`merge_lo` equation runs the erased state under `lt` and obtains exactly the
erasure of the tagged result
(`Correctness/OccurrenceErasureMerges.lean:875`).  The symmetric
`merge_hi` equation states the identical relation for the backward-filling
machine (`Correctness/OccurrenceErasureMerges.lean:2019`).
Neither theorem assumes an order law: the result follows from value-only
comparator observations and whole-entry movement.

This node includes the straight and galloping phases of both concrete merge
engines, but not `merge_at`, policy collapse, or the top-level scan.

## Depends on

- [Primitive evaluators ignore occurrence origins](occurrence-erasure-primitives.md)
- [`merge_lo` transcription](../../../transcription/merge-lo.md)
- [`merge_hi` transcription](../../../transcription/merge-hi.md)

## Proof depends on

- [`merge_getmem`](../../../transcription/merge-getmem.md)
- [`merge_freemem`](../../../transcription/merge-freemem.md)
- [`gallop_left`](../../../transcription/gallop-left.md)
- [`gallop_right`](../../../transcription/gallop-right.md)
- [`SortSlice` primitives](../../../transcription/sortslice-primitives.md)

## Sources

- [Functional-correctness theorem contract](../../../../sources/toplevel-theorems.md#functional-correctness)
