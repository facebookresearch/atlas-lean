---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.powerloopInputBounds
---

# `powerloop` input arithmetic bounds

For adjacent nonempty runs beginning at `s1`, assume
`s1 + n1 + n2 ≤ n` and `n ≤ PY_LIST_MAX`. For the exact expressions
`a = 2*s1+n1` and `b = 2*s1+2*n1+n2`, prove
`0 ≤ a < b < 2*n` and that both values are below `2^63`. This is the
initialization lemma that connects CPython's allocation-backed input domain to
the finite-width model without modular wraparound.

## Depends on

- [Finite-width implementation model](../transcription/word-model.md)

## Sources

- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [CPython arithmetic-slack explanation](../../sources/listsort.md#the-merge-pattern)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
