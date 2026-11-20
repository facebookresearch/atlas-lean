---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.binarysort_correct
---

# `binarysort` preserves and extends stable sortedness

For occurrence-carrying keys and a `MergeState` whose comparator is exactly
`occurrenceComparator lt`, assume:

- `BoolStrictWeakOrder lt`;
- the source bounds `1 ≤ n`, `ok ≤ n`, and `n ≤ MAX_MINRUN`;
- the source range and synchronized-values mode invariants;
- `Sorted (occurrenceComparator lt)` on the initial `ok`-prefix; and
- `StableOccurrencePermutation lt canonical` on the whole target range.

Then the actual traced `binarysort` execution returns a result with its
`BinarysortSafetyPost`, exact `Sorted` and `StableOccurrencePermutation` posts
on `[base, base + n)`, a whole-entry permutation of that range, and both the
shared `EqualOutsideRange` frame and pointwise before/after frame facts.  This
statement and proof are machine-checked at
`Code/Correctness/BinarysortCorrectness.lean:1231`; its exported post
is defined at `Code/Correctness/BinarysortCorrectness.lean:1209`.

The whole-range stability premise is intentional. Binary insertion preserves
the relative order already present among comparator-equivalent occurrences,
but cannot repair an equal-key suffix whose origins were noncanonical before
that suffix is inserted.

## Review pins

- Equality takes the upper-bound/right branch: the actual traced search
  returns position `2` past two older equal occurrences, and the actual traced
  sort inserts the pivot after them
  (`Code/Correctness/BinarysortCorrectness.lean:1301`).
- A nonzero-base execution sorts only `[1,4)`, leaves both outside sentinels
  unchanged, and retains equal-key origin order
  (`Code/Correctness/BinarysortCorrectness.lean:1305`).

These are executable theorem regressions, not observations from the proof
body.

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [binarysort](../../transcription/binarysort.md)
- [binarysort safety](../safety/binarysort-safe.md)

## Sources

- [Verbatim `binarysort`](../../../sources/listobject-excerpts.md#binarysort)
- [Mathlib list-sort prior art](../../../sources/mathlib-prior-art.md#sortedness-and-permutation)
