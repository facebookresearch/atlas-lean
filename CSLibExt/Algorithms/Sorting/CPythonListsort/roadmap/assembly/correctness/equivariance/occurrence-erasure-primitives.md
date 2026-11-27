---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.eraseOccurrenceBinarysort
---

# Primitive evaluators ignore occurrence origins

Occurrence tags are proof ghosts: execution may move them with entries, but
must not inspect them.  Structural erasure is defined for entries, slices,
temporary storage, merge states, and complete top-level results
(`Correctness/OccurrenceErasure.lean:28`, `:34`, `:45`, `:52`,
and `:67`; definitions).  The projected occurrence comparator is literally
the original value comparator
(`Correctness/OccurrenceErasure.lean:75`).

The primitive simulation proves exact evaluator equations rather than only an
output permutation.  It covers allocation and storage replacement through
`eraseOccurrenceMergeGetmem`
(`Correctness/OccurrenceErasure.lean:448`), both hinted gallops
(`Correctness/OccurrenceErasure.lean:649` and `:683`), slice
reversal (`Correctness/OccurrenceErasure.lean:769`), natural-run
detection (`Correctness/OccurrenceErasure.lean:1010`), and
binary insertion (`Correctness/OccurrenceErasure.lean:1169`).
Each equation erases the tagged result structurally, preserving payloads and
all non-key control fields.

This node is deliberately separate from merge and whole-scan erasure: its
completion does not by itself connect the public tagged and untagged sorts.

## Depends on

- [Boolean strict-weak-order specification](../order-and-stability.md)
- [Occurrence-tagged stability specification](../stable-spec.md)
- [Unscanned suffix matches the input snapshot](../scan-remainder-matches.md)
- [`MergeState`](../../../transcription/merge-state.md)
- [list_sort_impl](../../../transcription/list-sort-impl.md)

## Proof depends on

- [`SortSlice` primitives](../../../transcription/sortslice-primitives.md)
- [`merge_getmem`](../../../transcription/merge-getmem.md)
- [`merge_freemem`](../../../transcription/merge-freemem.md)
- [`gallop_left`](../../../transcription/gallop-left.md)
- [`gallop_right`](../../../transcription/gallop-right.md)
- [`reverse_slice` transcription](../../../transcription/reverse-slice.md)
- [`count_run` transcription](../../../transcription/count-run.md)
- [`binarysort` transcription](../../../transcription/binarysort.md)

## Sources

- [Functional-correctness theorem contract](../../../../sources/toplevel-theorems.md#functional-correctness)
