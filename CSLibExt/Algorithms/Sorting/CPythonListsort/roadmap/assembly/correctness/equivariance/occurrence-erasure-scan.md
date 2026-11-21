---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.eraseOccurrenceListSort
---

# The complete tagged sort erases to the untagged sort

Structural occurrence erasure commutes through the remaining assembly layers:
`merge_at` (`Correctness/OccurrenceErasureScan.lean:338`),
`found_new_run` (`Correctness/OccurrenceErasureScan.lean:977`),
final collapse (`Correctness/OccurrenceErasureScan.lean:987`),
and the recursive scan
(`Correctness/OccurrenceErasureScan.lean:998`).  The raw
`listSortImpl?` bridge then covers initialization, both reverse phases, small
inputs, failure/fuel branches, cleanup, and the input-size guard
(`Correctness/OccurrenceErasureScan.lean:1011`).

The public theorem is premise-free: for every Boolean comparator, reverse
flag, and validated `ListSortInput`, ordinary execution equals the tagged
execution mapped through `eraseOccurrenceListSortImplResult`
(`Correctness/OccurrenceErasureScan.lean:1069`).  This is the
machine-checked tag-erasure boundary consumed by `listsort_correct`; it makes
the safety and correctness headlines refer to the same untagged evaluator.

## Depends on

- [Primitive evaluators ignore occurrence origins](occurrence-erasure-primitives.md)
- [list_sort_impl](../../../transcription/list-sort-impl.md)

## Proof depends on

- [Merge evaluators ignore occurrence origins](occurrence-erasure-merges.md)
- [`merge_at` transcription](../../../transcription/merge-at.md)
- [`found_new_run` transcription](../../../transcription/found-new-run.md)
- [`merge_force_collapse` transcription](../../../transcription/merge-force-collapse.md)
- [`count_run` transcription](../../../transcription/count-run.md)
- [`binarysort` transcription](../../../transcription/binarysort.md)

## Sources

- [Functional-correctness theorem contract](../../../../sources/toplevel-theorems.md#functional-correctness)
