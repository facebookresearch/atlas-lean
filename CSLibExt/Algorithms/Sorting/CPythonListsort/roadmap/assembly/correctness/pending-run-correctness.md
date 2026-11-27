---
declaration: def
origin: bridged
statement: formalized
lean: CPythonListsort.PendingRunsCorrect
---

# Pending-run correctness invariant

Define `PendingRunsCorrect lt input state scanned`: `PendingLayout` holds,
every pending run is sorted, and concatenating the carried occurrence-tagged
pending runs satisfies the shared `StableOccurrencePermutation` predicate
against exactly
`tagOccurrences input[basekeys .. basekeys + scanned)`. Tag the whole input
before extracting that segment so origins remain absolute. The invariant
deliberately says nothing about the unscanned suffix and embeds no comparator
law.

## Depends on

- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Pending-run layout invariant](../../policy/pending-layout.md)

## Sources

- [Functional-correctness theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
- [Verbatim pending-run layout](../../../sources/listobject-excerpts.md#merge-state)
