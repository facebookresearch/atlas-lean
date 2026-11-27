---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.powerloopTraceSafety
---

# `powerloop` trace safety

For valid adjacent nonempty runs and `n ≤ PY_LIST_MAX`, prove
`PowerloopTraceSafe 64` for the transcribed initial state. In particular, every
visited signed comparison has nonnegative operands, every subtraction is
nonnegative, and every executed left shift remains below `2^63`. The theorem
also proves the trace stops before the fuel boundary.

## Depends on

- [powerloop](../transcription/powerloop.md)
- [powerloop safety-trace specification](powerloop-trace-spec.md)

## Proof depends on

- [Natural quotient-bit recurrence result](powerloop-nat-result.md)
- [powerloop input arithmetic bounds](powerloop-input-bounds.md)
- [powerloop recurrence equivalence](powerloop-equivalence.md)

## Sources

- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [CPython arithmetic-slack explanation](../../sources/listsort.md#the-merge-pattern)
