---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.gallopLeft_correct_of_sorted
---

# `gallop_left` partition specification

Under a strict weak order, a valid sorted nonempty source range of length `n`
whose exact key array satisfies the shared `Sorted` predicate and that agrees
cell-for-cell with the reviewed slice, `hint < n`, and
`n ≤ PY_LIST_MAX`, prove that the actual `gallop_left` transcription succeeds
without fuel exhaustion and returns `k ≤ n` with `a[i] < key` for every
`i < k` and `¬(a[i] < key)` for every `k ≤ i < n`. Thus equivalent elements
remain on the right, exactly matching CPython's left-insertion convention.

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [gallop_left](../../transcription/gallop-left.md)

## Proof depends on

- [`gallop_left` safety](../safety/gallop-left-safe.md)

## Sources

- [CPython galloping explanation](../../../sources/listsort.md#galloping)
- [Verbatim `gallop_left`](../../../sources/listobject-excerpts.md#gallop-left)
