---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.countRun_correct
---

# `count_run` produces a stable sorted run

For occurrence-carrying keys and a `MergeState` whose comparator is exactly
`occurrenceComparator lt`, assume:

- `BoolStrictWeakOrder lt`;
- a positive, `PY_SSIZE_T_MAX`-representable remaining length in the supplied
  `SortSlice.RangeInBounds`;
- the source synchronized-values mode invariant; and
- `CountRunCanonicalRange` on the input range (the input occurrences already
  have increasing origins within comparator-equivalence classes).

Then the actual traced `count_run` execution returns its reviewed
`CountRunSafetyPost`, a length in `[1, nremaining]` satisfying the exact source
lower bound `nremaining = 1 ∨ 2 ≤ result.length`, exact shared `Sorted`
and `StableOccurrencePermutation` conclusions on the returned range, a
permutation of the whole key/payload entries in that range, and the shared
`EqualOutsideRange` frame.  The exported post, including that lower-bound
field, is defined at
`Correctness/CountRunCorrectness.lean:95`; the public theorem
that pins these conclusions and its exact-erasure join to `countRun_safe` is
machine-checked at
`Correctness/CountRunCorrectness.lean:1737`.

The canonical-origin premise is not a free top-level assumption.  The
unscanned-suffix invariant exports the exact bridge
`ScanRemainderMatches.countRunCanonicalRange` at
`Correctness/CountRunCorrectness.lean:69`; the underlying fact
that an absolute-origin canonical segment is stable relative to itself is
machine-checked at
`Correctness/CountRunCorrectness.lean:54`.  The scan-step node
must consume this bridge at the `count_run` call site.  Its whole-entry
companion has a direct bridge through the same key projection at
`Correctness/CountRunCorrectness.lean:82`.

The proof follows the transcribed evaluator rather than a replacement run
detector.  Its evaluator-facing stages are the ascending scan
(`Correctness/CountRunCorrectness.lean:253`), equal-block
reversal (`Correctness/CountRunCorrectness.lean:524`),
descending scan (`Correctness/CountRunCorrectness.lean:762`),
and final tail/whole reversal plus ascending extension
(`Correctness/CountRunCorrectness.lean:1065`).

## Source-to-declaration map

- The initial ascending probe in
  `sources/listobject-excerpts.md:652`–`657` is transcribed by
  `ascendingScan?` at `Transcription/CountRun.lean:58`; its
  functional theorem is `ascendingScan_correct` at
  `Correctness/CountRunCorrectness.lean:253`.
- The first/last direction gate in
  `sources/listobject-excerpts.md:658`–`674` is transcribed by
  `countRun?` at `Transcription/CountRun.lean:185` and is owned
  by the complete raw-evaluator theorem `countRun_raw_correct` at
  `Correctness/CountRunCorrectness.lean:1521`, not by
  `ascendingScan_correct`.
- `REVERSE_LAST_NEQ` in
  `sources/listobject-excerpts.md:632`–`642`, including its two call
  sites at `:695` and `:704`, is transcribed by `reverseLastEqual?` at
  `Transcription/CountRun.lean:82` and proved exact at
  `Correctness/CountRunCorrectness.lean:524`.
- The descending comparison loop in
  `sources/listobject-excerpts.md:681`–`695` is transcribed by
  `descendingScan?` at `Transcription/CountRun.lean:102` and its
  actual-evaluator induction starts at
  `Correctness/CountRunCorrectness.lean:762`.
- Final equal-tail reversal, whole-run reversal, and ascending extension in
  `sources/listobject-excerpts.md:696`–`708` are transcribed by
  `finishDescending?` at `Transcription/CountRun.lean:142` and
  composed at `Correctness/CountRunCorrectness.lean:1065`.

## Review pins

- The adversarial tagged run `[3, 2a, 2b, 1]` returns
  `[1, 2a, 2b, 3]`, pinning equal-block origin order through both reversal
  phases (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/CountRunCorrectness.lean:85`).
- An all-equal run remains in canonical origin order
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/CountRunCorrectness.lean:108`).
- A normalized descending prefix is extended by the actual final ascending
  scan, including stable placement of an equivalent boundary value
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/CountRunCorrectness.lean:130`).
- A nonzero-base execution reverses only its selected run and leaves both
  outside sentinels untouched
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/CountRunCorrectness.lean:124`).

These four items are executable theorem regressions, not proof-body
observations.

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [count_run](../../transcription/count-run.md)
- [Unscanned suffix matches the input snapshot](scan-remainder-matches.md)
- [count_run safety](../safety/count-run-safe.md)

## Proof depends on

- [Slice reversal preserves occurrence information](reverse-slice-correct.md)

## Sources

- [CPython run explanation](../../../sources/listsort.md#runs)
- [Verbatim `count_run`](../../../sources/listobject-excerpts.md#count-run)
