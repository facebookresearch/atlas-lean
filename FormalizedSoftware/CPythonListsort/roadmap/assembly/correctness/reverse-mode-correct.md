---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.reverseMode_correct
---

# Reverse mode implements the swapped order

Prove that CPython's reverse-mode pattern—reverse the input, run the stable
forward sort, then reverse the result—produces a stable result for the swapped
strict comparator. The theorem must retain occurrence tags through both
reversals so comparator-equivalent elements finish in original input order.
Do not feed the pre-reversed original tags directly to the forward scan
invariant: equal-key origins are decreasing at that point.  Consume the
reverse-oriented scan-transport theorem, whose mirrored-origin relabeling
connects the actual internal execution to a canonically tagged reversed
source, and prove that the final reversal restores increasing original-origin
order.  The internal certificate before that final reversal also carries
`EntrySnapshotPermutation`; prove that the final whole-slice reversal is a
whole-entry range permutation with the matching outside-range frame, and
export `EntrySnapshotPermutation` for the final state.  Reverse correctness
must therefore preserve keyed payload pairing as well as key-level occurrence
order.

`ReverseModeCorrectnessPost` exposes the raw scan-result equation, successful
return, fuel non-exhaustion, sortedness for the swapped comparator,
occurrence-level stability, and the whole-entry snapshot
(`Code/Correctness/ReverseModeCorrectness.lean:26`).  The theorem has
only the strict-weak-order law, validated input, and nontrivial size bounds as
premises (`Code/Correctness/ReverseModeCorrectness.lean:44`).  Inside
the proof, local facts establish that the transcribed final whole-range
reversal makes the resulting occurrence array exactly the reverse of the
pre-finish one, then derive all three exported semantic conclusions from that
equation
(`Code/Correctness/ReverseModeCorrectness.lean:62`,
`Code/Correctness/ReverseModeCorrectness.lean:86`, and
`Code/Correctness/ReverseModeCorrectness.lean:96`).  Those equality
facts are proof-body evidence, not additional fields of the public post.

There are two deliberately different views of the keyed final reversal.  The
physical C-facing trace selects only the `.values` phase in keyed mode
(`Code/Assembly/ListSortTrace.lean:118`), matching the
`reverse_slice(saved_ob_item, ...)` call.  Separately, the functional theorem
reasons directly about the paired-snapshot `finishListSort?` model.  The
phase selection is defined by `finalReversePhase`
(`Code/Assembly/ListSortSupport.lean:386`; definitional fidelity
evidence).  The structural erasure theorems are separate fidelity certificates
connecting that model to the phase-specific trace; they are not logical
premises of `reverseMode_correct`
(`Code/Assembly/ListSortSupport.lean:396` and
`Code/Assembly/ListSortTrace.lean:345`).  Thus the semantic proof
does not pretend that the C performs a second keyed two-phase reversal.  The
phase trace still returns a paired-snapshot semantic update rather than a
literal intermediate separate-array C store; that declared abstraction
boundary is documented at
`Code/Assembly/ReverseSliceSafety.lean:80` and remains part of the
human-reviewed C-to-model transcription, not a machine-checked C refinement.

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [Reverse-mode order and stability algebra](reverse-mode-algebra.md)
- [Reverse-oriented scan transport](reverse-scan-transport.md)
- [list_sort_impl](../../transcription/list-sort-impl.md)

## Proof depends on

- [Slice reversal preserves occurrence information](reverse-slice-correct.md)

## Sources

- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
