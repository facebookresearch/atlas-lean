---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.gallopRight_correct_of_sorted
---

# `gallop_right` partition specification

Under a strict weak order, a valid sorted nonempty source range of length `n`
whose exact key array satisfies the shared `Sorted` predicate and that agrees
cell-for-cell with the reviewed slice, `hint < n`, and
`n ≤ PY_LIST_MAX`, prove that the actual `gallop_right` transcription succeeds
without fuel exhaustion and returns `k ≤ n` with `¬(key < a[i])` for every
`i < k` and `key < a[i]` for every `k ≤ i < n`. Thus equivalent elements
remain on the left. Keep this equality behavior separate from `gallop_left`.

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [gallop_right](../../transcription/gallop-right.md)

## Proof depends on

- [`gallop_right` safety](../safety/gallop-right-safe.md)

## Sources

- [CPython galloping explanation](../../../sources/listsort.md#galloping)
- [Verbatim `gallop_right`](../../../sources/listobject-excerpts.md#gallop-right)
