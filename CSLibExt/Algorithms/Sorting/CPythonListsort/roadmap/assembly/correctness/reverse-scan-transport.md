---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.reverseScanTransport_correct
---

# Reverse-oriented scan transport

The forward scan theorem cannot be applied directly to the actual
`reverse = true` execution.  `list_sort_impl` first reverses the complete
occurrence-tagged slice, so equal values carry decreasing original origins;
the forward `ScanRemainderEntriesMatch` and `CountRunCanonicalRange`
predicates intentionally require the canonical increasing-origin order.

Define the mirrored-origin relabeling for a slice of length `n` and prove that
all comparator observations and every data-moving evaluator used by the scan
commute with this relabeling: comparisons ignore origins, while reads, writes,
reversals, binary insertion, and merges move whole entries.  Show that the
actual pre-reversed tagged slice is the mirrored relabeling of the canonically
tagged reversed source.  Apply the forward scan and final-collapse theorems to
that canonical execution, transporting `ScanRemainderEntriesMatch`,
`PendingRunsCorrect`, and `EntrySnapshotPermutation` across the relabeling,
then transport the result back.  This yields the reverse-oriented internal
certificate needed before the final whole-slice reversal; it must not assume
the forward predicates directly on the pre-reversed original tags.

The formal bridge names both executions.  `canonicalReverseScanState` starts
from the canonically tagged reversed source, while `actualReverseScanState`
mirrors those origins back to the labels carried by the real initial reversal
(`Correctness/ReverseScanTransport.lean:34` and
`Correctness/ReverseScanTransport.lean:41`).  The bridge is not
merely extensional on the key array: `actualReverseScanState_data` proves the
exact paired-entry reversal, and
`actualReverseScanState_eq_initial_with_reversed_data` identifies the complete
initialized state (`Correctness/ReverseScanTransport.lean:48`
and `Correctness/ReverseScanTransport.lean:62`).

`ReverseScanTransportPost` retains the canonical proof packet, exact terminal,
collapse, and result mirrors, raw scan commutation, exact collapse and finish
equations, successful return and fuel facts, pre-finish sortedness,
reverse-stability, and the whole-entry snapshot
(`Correctness/ReverseScanTransport.lean:97`).  The public
theorem assumes only the strict-weak-order law, a validated input, and the
nontrivial top-level size bounds
(`Correctness/ReverseScanTransport.lean:148`).  Its proof calls
the complete forward scan theorem on the canonical reversed input, transports
the actual evaluator result through `mirrorListSortScan`, and derives the
three semantic pre-finish fields rather than assuming them
(`Correctness/ReverseScanTransport.lean:169`,
`Correctness/OriginRelabelScan.lean:1261`, invoked at
`Correctness/ReverseScanTransport.lean:180`; and
`Correctness/ReverseScanTransport.lean:229`,
`Correctness/ReverseScanTransport.lean:233`, and
`Correctness/ReverseScanTransport.lean:241`).

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Unscanned suffix matches the input snapshot](scan-remainder-matches.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [Origin-relabel equivariance support](equivariance/origin-relabel-equivariance.md)
- [Reverse-mode order and stability algebra](reverse-mode-algebra.md)
- [Complete scan and final-collapse correctness](scan-loop-correct.md)
- [list_sort_impl](../../transcription/list-sort-impl.md)

## Proof depends on

- [Policy and complete scan commute with origin relabeling](equivariance/scan-origin-equivariance.md)

## Sources

- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
- [Functional-correctness theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
