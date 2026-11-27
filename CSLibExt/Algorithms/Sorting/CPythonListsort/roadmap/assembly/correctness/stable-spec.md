---
declaration: def
origin: bridged
statement: formalized
lean: CPythonListsort.Stable
---

# Occurrence-tagged stability specification

Tag each input occurrence by its original index before sorting and carry that
tag through every modeled movement while exposing only the value to `lt`.
Export `StableOccurrencePermutation lt canonical output` as the shared
predicate requiring that `output` is a permutation of `canonical` and that
comparator-equivalent occurrences appear in increasing original-index order.
For a carried `ys : TaggedOutput α`, define `Stable lt xs ys` to be exactly
that predicate instantiated with `(tagOccurrences xs).toList` and
`ys.occurrences.toList`; export the definitional equivalence as a theorem.
`PendingRunsCorrect` consumes the same shared predicate with the absolute-origin
consumed segment as its canonical sequence. The externally observable array is
`ys.values`. Neither layer may retag the output existentially after the fact;
both distinguish duplicate occurrences and are used together with value-level
`List.Perm`, not as a replacement for permutation.

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)

## Sources

- [Top-level theorem contract](../../../sources/toplevel-theorems.md#functional-correctness)
- [Mathlib stability prior art](../../../sources/mathlib-prior-art.md#stability)
