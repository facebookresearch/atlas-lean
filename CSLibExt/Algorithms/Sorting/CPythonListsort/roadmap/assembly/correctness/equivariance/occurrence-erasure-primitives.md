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
(`Code/Correctness/OccurrenceErasure.lean:20`, `:26`, `:37`, `:44`,
and `:59`; definitions).  The projected occurrence comparator is literally
the original value comparator
(`Code/Correctness/OccurrenceErasure.lean:67`).

The primitive simulation proves exact evaluator equations rather than only an
output permutation.  It covers allocation and storage replacement through
`eraseOccurrenceMergeGetmem`
(`Code/Correctness/OccurrenceErasure.lean:440`), both hinted gallops
(`Code/Correctness/OccurrenceErasure.lean:641` and `:675`), slice
reversal (`Code/Correctness/OccurrenceErasure.lean:761`), natural-run
detection (`Code/Correctness/OccurrenceErasure.lean:1002`), and
binary insertion (`Code/Correctness/OccurrenceErasure.lean:1161`).
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
