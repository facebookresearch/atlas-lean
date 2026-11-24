---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mirrorBinarysort
---

# Origin-relabel equivariance support

Reverse-mode reasoning needs to compare two executions that carry the same
values and payloads but opposite absolute-origin labels.  `mirrorOrigin` is a
total involution: an origin below the input extent `size` is sent to
`size - 1 - origin`, while an out-of-range origin is left fixed.  The fixed
outside branch matters for fabricated or stale temporary cells; plain
truncated subtraction would not be an involution there
(`Correctness/OriginRelabelEquivariance.lean:31`, definition;
`Correctness/OriginRelabelEquivariance.lean:39`, theorem).

The relabeling is lifted through occurrences, synchronized entries, slices,
temporary storage, and complete merge states.  By definition it changes
neither values nor payloads, pending-run geometry, nor allocation metadata
(`Correctness/OriginRelabelEquivariance.lean:52` and
`Correctness/OriginRelabelEquivariance.lean:72`; definitional
evidence).  Comparator preservation is theorem-pinned by
`occurrenceComparator_mirror`
(`Correctness/OriginRelabelEquivariance.lean:159`).  The module
also exports exact commutation lemmas for the data-moving primitives used
before the merge layer: reads and writes
(`Correctness/OriginRelabelEquivariance.lean:174` and
`Correctness/OriginRelabelEquivariance.lean:182`),
single-entry copies
(`Correctness/OriginRelabelEquivariance.lean:234` and
`Correctness/OriginRelabelEquivariance.lean:248`),
`memcpyCore?` and complete `memmove?`
(`Correctness/OriginRelabelEquivariance.lean:292` and
`Correctness/OriginRelabelEquivariance.lean:336`), and slice
reversal (`Correctness/OriginRelabelEquivariance.lean:390`).
The two largest public pins in this layer are `mirrorCountRun`
(`Correctness/OriginRelabelEquivariance.lean:591`) and
`mirrorBinarysort`
(`Correctness/OriginRelabelEquivariance.lean:730`).

Ordinary `PendingRunsCorrect` is deliberately **not** claimed for a mirrored
state: mirroring reverses the origin order used by its stability clause.
`CanonicalMirroredPendingRunsCorrect` instead requires ordinary layout and
sortedness on the real mirrored state while checking stability after applying
the involution back to its pending keys
(`Correctness/OriginRelabelEquivariance.lean:811`, definition).
The analogous whole-entry and suffix relations are
`CanonicalMirroredEntrySnapshotPermutation` and
`CanonicalMirroredScanRemainderEntriesMatch`
(`Correctness/OriginRelabelEquivariance.lean:823` and
`Correctness/OriginRelabelEquivariance.lean:831`, definitions).
Forward certificates transport into those reverse-oriented relations, and
unmirroring recovers the exact signed forward predicates
(`Correctness/OriginRelabelEquivariance.lean:850`,
`Correctness/OriginRelabelEquivariance.lean:867`,
`Correctness/OriginRelabelEquivariance.lean:882`,
`Correctness/OriginRelabelEquivariance.lean:893`,
`Correctness/OriginRelabelEquivariance.lean:903`, and
`Correctness/OriginRelabelEquivariance.lean:920`).

The nonidentity regression uses kernel reduction via `decide`: origin zero at
extent four becomes origin three, and the second application restores the
original occurrence
(`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/OriginRelabelEquivariance.lean:23`).

This primitive support node does not assert merge or whole-scan commutation.
Those peer-scale obligations are explicit downstream nodes:
[merge evaluator equivariance](merge-origin-equivariance.md),
[policy/scan equivariance](scan-origin-equivariance.md), and the separate
[reverse-mode algebra](../reverse-mode-algebra.md).  Keeping the layers separate
prevents a primitive theorem from being reported as the top-level reverse
result.

## Depends on

- [Boolean strict-weak-order specification](../order-and-stability.md)
- [Pending-run correctness invariant](../pending-run-correctness.md)
- [Unscanned suffix matches the input snapshot](../scan-remainder-matches.md)
- [Whole-entry snapshot permutation](../entry-snapshot-permutation.md)

## Proof depends on

- [`SortSlice` primitives](../../../transcription/sortslice-primitives.md)
- [`reverse_slice` transcription](../../../transcription/reverse-slice.md)
- [`count_run` transcription](../../../transcription/count-run.md)
- [`binarysort` transcription](../../../transcription/binarysort.md)

## Sources

- [Verbatim movement primitives](../../../../sources/listobject-excerpts.md#sortslice-primitives)
- [Verbatim reversal](../../../../sources/listobject-excerpts.md#reverse-slice)
- [Verbatim run detection](../../../../sources/listobject-excerpts.md#count-run)
- [Verbatim binary insertion](../../../../sources/listobject-excerpts.md#binarysort)
- [Functional-correctness theorem contract](../../../../sources/toplevel-theorems.md#functional-correctness)
