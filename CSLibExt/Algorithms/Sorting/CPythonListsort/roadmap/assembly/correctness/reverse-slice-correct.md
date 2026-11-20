---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.sortsliceReverseTraced_correct
---

# Exact slice-reversal correctness

For a valid half-open slice, prove that the actual `reverse_slice`
transcription returns the unchanged prefix, the reversed middle, and the
unchanged suffix. It preserves the permutation of whole key/value entries and
is an involution. Lift the exact result through the genuinely traced
`sortslice_reverse` execution while retaining its synchronized values-mode,
safety, fuel, and erasure certificate.

As on the [safety node](../safety/reverse-slice-safe.md), the Lean evaluator
totalizes `n = 0`, including a one-past-end base. This is a model-domain
extension: CPython decrements the exclusive high pointer before its loop test,
and every reviewed C call site supplies a positive length.

## Depends on

- [Slice reversal](../../transcription/reverse-slice.md)

## Proof depends on

- [Slice-reversal safety](../safety/reverse-slice-safe.md)

## Sources

- [Verbatim `reverse_slice`](../../../sources/listobject-excerpts.md#reverse-slice)
- [Verbatim `sortslice_reverse`](../../../sources/listobject-excerpts.md#sortslice-reverse)
