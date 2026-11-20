---
declaration: def
origin: bridged
statement: formalized
lean: CPythonListsort.EntrySnapshotPermutation
---

# Whole-entry snapshot permutation

Define `EntrySnapshotPermutation source current`: the complete current
`SortSliceEntry` array is a permutation of the source array after its keys
have been tagged with absolute occurrence indices.  Because the permutation
ranges over whole entries, every optional payload remains paired with the key
occurrence with which it entered the sort.  This is the persistent payload
invariant carried across scan iterations; it complements
`PendingRunsCorrect`, which deliberately speaks only about keys, and
`ScanRemainderEntriesMatch`, which speaks only about the untouched suffix.

Validated keyed and unkeyed inputs establish the invariant when
`initialMergeState` installs `ListSortInput.withOccurrenceKeys`.  A local
operation preserves it when its changed range is a whole-entry permutation,
its range is explicitly in bounds, and `SortSlice.EqualOutsideRange` frames
the prefix and suffix.  These are exactly the entry-permutation and frame
fields exported by the local `binarysort` and `count_run` correctness posts.

`EntrySnapshotPermutation` is defined at
`Code/Correctness/EntrySnapshotPermutation.lean:21`.

## Review pins

- Validated initialization is proved by
  `EntrySnapshotPermutation.initial_merge_state`
  (`Code/Correctness/EntrySnapshotPermutation.lean:47`), with
  explicit keyed and unkeyed specializations at
  `Code/Correctness/EntrySnapshotPermutation.lean:56` and
  `Code/Correctness/EntrySnapshotPermutation.lean:64`.
- A framed, in-bounds local whole-entry permutation is promoted to a
  whole-array permutation by
  `wholeEntries_perm_of_range_perm_and_frame`
  (`Code/Correctness/EntrySnapshotPermutation.lean:101`), and
  preserves the invariant through `EntrySnapshotPermutation.preserve_local`
  (`Code/Correctness/EntrySnapshotPermutation.lean:152`).
- The concrete keyed anti-vacuity regression keeps both tagged keys fixed but
  changes one payload and proves that the invariant rejects the result
  (`Code/Correctness/EntrySnapshotPermutation.lean:179`).

These are theorem/regression citations; the declaration at line 21 is only
the invariant definition.

## Depends on

- [Unscanned suffix matches the input snapshot](scan-remainder-matches.md)
- [`sortslice` model and movement primitives](../../transcription/sortslice-primitives.md)

## Sources

- [Functional-correctness theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
