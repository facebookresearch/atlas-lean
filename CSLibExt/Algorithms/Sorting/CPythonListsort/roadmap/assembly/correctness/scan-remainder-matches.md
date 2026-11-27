---
declaration: structure
origin: bridged
statement: formalized
lean: CPythonListsort.ScanRemainderEntriesMatch
---

# Unscanned suffix matches the input snapshot

Define the comparator-independent proposition
`ScanRemainderMatches input state scanned`.  It states, with explicit bounds,
that the keys in the still-unscanned half-open range
`[basekeys + scanned, basekeys + listlen)` are exactly the corresponding
absolute-origin segment of `tagOccurrences input`.

Retain that key-only interface, and add the companion
`ScanRemainderEntriesMatch source state scanned`.  It compares the same
bounded range as whole `SortSliceEntry` records against a source slice whose
keys were tagged at their absolute full-slice indices.  The tagging transform
must preserve each optional payload.  Initialization runs through
`initialMergeState` with the exact `hasKeyfunc` mode of an arbitrary validated
`ListSortInput`, so the claim covers both keyed and unkeyed construction.
`ScanRemainderEntriesMatch` is defined at
`Correctness/ScanRemainder.lean:109`; the retained key-only
`ScanRemainderMatches` interface is defined at
`Correctness/ScanRemainder.lean:129`.

Keep both propositions separate from `PendingRunsCorrect`, which intentionally
owns only the consumed prefix.  A mutation confined to the consumed range
preserves the unscanned whole-entry snapshot, and consuming a new range
advances it when the later suffix is framed; neither statement claims that
this node itself proves correctness of the newly consumed prefix.  Include
concrete pins that a keyed payload survives occurrence tagging, that
nonzero-base absolute origins cannot be replaced by local origins even when
visible values agree, and that a state accepted by `PendingRunsCorrect` may
still be rejected because its unscanned suffix is wrong.

## Review pins

- Whole-slice occurrence tagging preserves the complete payload projection by
  `tagSortSliceOccurrences_payloads`
  (`Correctness/ScanRemainder.lean:61`).  The concrete keyed
  constructor regression keeps `some 42` paired with key `7@0`
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/ScanRemainder.lean:17`).
- Initialization for an arbitrary validated `ListSortInput`, with its exact
  `hasKeyfunc` mode, is proved by
  `scanRemainderEntriesMatch_initial_listSortInput`
  (`Correctness/ScanRemainder.lean:394`).
- A consumed-range update preserves the whole-entry suffix by
  `ScanRemainderEntriesMatch.preserve_consumed_update`
  (`Correctness/ScanRemainder.lean:273`), and consuming a new
  framed interval advances it by `ScanRemainderEntriesMatch.advance`
  (`Correctness/ScanRemainder.lean:299`).
- The wrong-suffix anti-vacuity regression exhibits a state accepted by
  `PendingRunsCorrect` and rejected by `ScanRemainderMatches`
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/ScanRemainder.lean:57`).
- The nonzero-base regression has matching visible values and a deliberately
  matching zero-based prefix, but is rejected for the wrong absolute origin
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/ScanRemainder.lean:106`).

Each item above cites its theorem or executable regression; the two predicate
locations in the opening section are definitions, not pinning theorems.

## Depends on

- [`sortslice` primitives stay in bounds](../safety/sortslice-safe.md) (statement
  dependency for the validated values-mode support)
- [`sortslice` model and movement primitives](../../transcription/sortslice-primitives.md)
  (statement dependency for the raw `SortSlice` representation)
- [`list_sort_impl`](../../transcription/list-sort-impl.md)

## Proof depends on

- [Pending-run correctness invariant](pending-run-correctness.md) (used only by
  the wrong-suffix anti-vacuity regression)

## Sources

- [Functional-correctness theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
