---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.minrunExponentCharacterization
---

# `merge_init` exponent characterization

For `listlen ≤ PY_LIST_MAX`, prove that the 64-step initialization loop stops
and returns the least exponent `e` such that `listlen / 2^e < MAX_MINRUN`.
Derive `e < 64` (and the selected-platform sharper bound `e ≤ 60`) as named
corollaries of this one least-exponent theorem. These bounds justify the
64-bit exponent representation and the later signed-addition proof; they do
not turn C's narrower 32-bit mask expression into an exact mathematical mask.
The proof consumes the unconditional exponent bridge from the initialization
node, not its conditional exact-mask clause.

## Depends on

- [merge_init minrun initialization](../transcription/merge-init-minrun.md)
- [Finite-width implementation model](../transcription/word-model.md)

## Proof depends on

- [merge_init exponent and conditional mask equivalence](minrun-init-equivalence.md)

## Sources

- [CPython adaptive-minrun explanation](../../sources/listsort.md#computing-minrun)
- [Verbatim `merge_init`](../../sources/listobject-excerpts.md#merge-init)
