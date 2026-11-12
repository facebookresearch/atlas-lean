---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listsort_correct
---

# `listsort_correct`

For a strict-weak-order Boolean comparator and either value of the `reverse`
flag, and for `xs.size ≤ PY_LIST_MAX`, the assembled listsort model returns a
sorted, stable permutation of its input snapshot under the requested relation:
the original comparator in forward mode and its argument-swapped relation in
reverse mode.

First state the implementation-level correctness theorem over a proof-carrying
`ListSortInput`, including keyed inputs, and the public `listSort?` entry point.
It must export `EntrySnapshotPermutation` between the validated input slice and
the final occurrence-carrying slice (or an explicitly equivalent whole-entry
permutation statement), so every key occurrence remains paired with its
original optional payload.  Then derive the displayed `Array` theorem as the
explicit unkeyed corollary obtained from `ListSortInput.unkeyed xs`.  That
corollary projects the whole-entry fact to the displayed value-level
permutation; it does not replace the required stronger keyed result.  Neither
theorem may invoke raw `listSortImpl?` on an unconstrained `SortSlice`; any
separately exported raw generalization retains the premise
`SortSlice.ValuesModeInvariant hasKeyfunc input`.

The implementation-level result packet is `ListSortCorrectnessPost`. Its first
field is an exact equation to the occurrence-enriched `listSort?` execution,
followed by successful return, fuel non-exhaustion, requested-order sortedness,
occurrence-level stability, and whole-entry snapshot preservation
(`Code/Correctness/ListSortCorrectness.lean:26`). Completion is
therefore exported as an actual `some result`; it is not inferred merely from
`fuelExhausted = false`. The public companion
`ListSortCorrectnessPost.untaggedResultEq` uses structural erasure to pin the
same certificate to the ordinary untagged execution
(`Code/Correctness/ListSortCorrectness.lean:47`).

The zero/one-element bypass is proved for an arbitrary Boolean comparator,
without an order-law premise
(`Code/Correctness/ListSortCorrectness.lean:87`). The nontrivial
forward and reverse branches are proved separately and then selected on the
public Boolean flag
(`Code/Correctness/ListSortCorrectness.lean:171`,
`Code/Correctness/ListSortCorrectness.lean:235`, and
`Code/Correctness/ListSortCorrectness.lean:324`). The public
ordinary-array corollary has exactly the signed assumptions—one
`BoolStrictWeakOrder`, the reverse flag, an input array, and
`xs.size ≤ PY_LIST_MAX`. It exports both exact execution equations: ordinary
`listSort? lt` returns the structurally erased result, and occurrence-enriched
`listSort? (occurrenceComparator lt)` returns the tag-carrying result used for
stability. Requested-order sortedness, ordinary stability, and value
permutation are then stated on that connected result
(`Code/Correctness/ListSortCorrectness.lean:360`). Thus tags cannot
be manufactured after execution, and correctness and safety concern the same
ordinary evaluator.

For direct keyed-array API discovery, `listsort_correct_keyed` specializes the
same implementation theorem through `ListSortInput.keyed`. It exposes the
ordinary evaluator equation together with the complete
`ListSortCorrectnessPost`; its `sorted`, `stable`, and `entrySnapshot` fields
are respectively the key-order, equal-key occurrence-order, and complete
key/origin/payload permutation guarantees. This is a convenience corollary,
not a new correctness premise or roadmap obligation
(`Code/Correctness/ListSortCorrectness.lean:338`).

Two kernel-checked inhabited semantic witnesses guard the public boundary.  A
keyed reverse input with duplicate keys produces an actual `listSort?` result whose
observable contract includes requested-order sortedness, increasing origins
inside equal-key classes, and key/payload snapshot preservation
(`Code/Correctness/ListSortCorrectness.lean:446`). Empty and
singleton reverse-mode calls have exact successful result views, including the
retained singleton payload
(`Code/Correctness/ListSortCorrectness.lean:477`). Two additional
exact-output witnesses execute the duplicate-key input in forward and reverse
mode and compare the full key/origin/payload output with literal expected
lists.  Those two are explicitly compiler-checked `native_decide` proof leaves
at `Code/Correctness/ListSortCorrectness.lean:543` and `:561`; neither
is consumed by a theorem.

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [Reverse-mode order and stability algebra](reverse-mode-algebra.md)
- [Primitive evaluators ignore occurrence origins](equivariance/occurrence-erasure-primitives.md)
- [list_sort_impl](../../transcription/list-sort-impl.md)
- [Finite-width implementation model](../../transcription/word-model.md)
- [sortslice primitive safety](../safety/sortslice-safe.md)

## Proof depends on

- [Complete scan and final-collapse correctness](scan-loop-correct.md)
- [Reverse mode implements the swapped order](reverse-mode-correct.md)
- [The complete tagged sort erases to the untagged sort](equivariance/occurrence-erasure-scan.md)
- [Slice reversal preserves occurrence information](reverse-slice-correct.md)
- [list_sort_impl fuel adequacy](../safety/termination.md)

## Sources

- [Functional-correctness theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
