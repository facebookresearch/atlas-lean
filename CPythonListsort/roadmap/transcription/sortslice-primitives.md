---
declaration: structure
origin: cited
statement: formalized
lean: CPythonListsort.SortSlice
---

# `sortslice` model and movement primitives

Model synchronized key/value slices and the copy, increment, decrement,
`memcpy`, `memmove`, and advance operations used by the merge code. The v1
model uses arrays and indices instead of raw pointers while preserving aliasing
and movement direction relevant to observable results.

The incrementing and decrementing copies accept distinct destination and
source stores, as the C helpers do; their shared-store forms are derived
specializations. Represent `memcpy` source provenance explicitly as same
backing or distinct backing, never by structural equality of array contents.
Same-backing calls admit only disjoint half-open ranges, while overlapping
same-store movement is modeled by `memmove`. The general `memmove` source uses
the same explicit provenance: distinct backing copies between two stores,
while same backing selects the overlap-safe forward or backward traversal.

## Depends on

- [Finite-width implementation model](word-model.md)

## Sources

- [Verbatim `sortslice` layout and primitives](../../sources/listobject-excerpts.md#sortslice-primitives)
