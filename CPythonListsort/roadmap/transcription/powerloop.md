---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.powerloop
---

# `powerloop`

Transcribe CPython's finite-width loop: initialize doubled midpoints `a` and
`b`, increment the result before each test, subtract `n` when both quotient
bits are one, stop when only `b` crosses `n`, and otherwise left-shift both
values. A fixed 64-step total loop models the C loop; exhaustion is exposed in
the returned trace rather than hidden with `partial`.

## Depends on

- [Finite-width implementation model](word-model.md)

## Human transcription review

Check initialization (`2*s1+n1`, then `a+n1+n2`), signed comparisons, branch
order, subtraction of `n` from both values, the pre-test result increment, and
the exact left-shift placement. This page makes no node-power correctness
claim.

## Sources

- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [CPython merge-pattern explanation](../../sources/listsort.md#the-merge-pattern)
