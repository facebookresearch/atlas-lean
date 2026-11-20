---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.stable_reversedSource_mirror_reverse
---

# Reverse-mode order and stability algebra

`swappedComparator` reverses comparator arguments and `requestedComparator`
selects it exactly when the public reverse flag is true
(`Code/Correctness/ReverseModeAlgebra.lean:17` and
`Code/Correctness/ReverseModeAlgebra.lean:21`).  Strict weak orders
are closed under that swap, and reversing a forward-sorted array is sorted by
the swapped relation
(`Code/Correctness/ReverseModeAlgebra.lean:44` and
`Code/Correctness/ReverseModeAlgebra.lean:84`).

The intermediate reverse-mode stability predicate records decreasing origins
inside an equivalence class; reversing its output restores ordinary increasing
origin order for the swapped comparator
(`Code/Correctness/ReverseModeAlgebra.lean:112` and
`Code/Correctness/ReverseModeAlgebra.lean:124`).  Canonically tagging
a reversed source and mirroring its origins is exactly the original tagged
source in reverse, including optional payloads
(`Code/Correctness/ReverseModeAlgebra.lean:302` and
`Code/Correctness/ReverseModeAlgebra.lean:311`).

The principal algebra theorem combines those facts: a stable result for the
physically reversed source becomes a stable result for the requested swapped
comparator after origin mirroring and the final reversal
(`Code/Correctness/ReverseModeAlgebra.lean:390`).  The whole-entry
snapshot transport used beside it is independently theorem-pinned at
`Code/Correctness/ReverseModeAlgebra.lean:344`.

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [Origin-relabel equivariance support](equivariance/origin-relabel-equivariance.md)

## Sources

- [Functional-correctness theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
