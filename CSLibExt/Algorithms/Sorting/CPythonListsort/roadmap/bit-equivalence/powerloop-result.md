---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.powerloopResult
---

# `powerloop` terminating-result characterization

For valid adjacent nonempty runs with total length `n ≤ PY_LIST_MAX`, prove
that the transcribed function does not exhaust its 64-step bound and returns
one plus the least zero-based quotient-bit position at which the exact
doubled-midpoint fractions differ. This is the one-based PowerSort node power
and the single public result connecting CPython's `powerloop` return value to
the mathematical specification.

## Depends on

- [powerloop](../transcription/powerloop.md)
- [Natural-number powerloop specification](powerloop-nat-spec.md)

## Proof depends on

- [Natural quotient-bit recurrence result](powerloop-nat-result.md)
- [powerloop recurrence equivalence](powerloop-equivalence.md)
- [powerloop trace safety](powerloop-trace-safety.md)

## Sources

- [CPython quotient-bit explanation](../../sources/listsort.md#the-merge-pattern)
- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [Munro-Wild node power](../../sources/munro-wild-powersort-notes.md#node-power)
