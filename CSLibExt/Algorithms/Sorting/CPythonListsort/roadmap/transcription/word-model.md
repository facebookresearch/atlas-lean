---
declaration: abbrev
origin: bridged
statement: formalized
lean: CPythonListsort.PySSize
---

# Finite-width implementation model

Represent nonnegative `Py_ssize_t` values as `BitVec 64`, with signed
comparison and arithmetic helpers matching the C operations used by listsort.
The validity predicate restricts words to `0 .. PY_SSIZE_T_MAX`. Fix the
selected platform's 8-byte pointer size and define
`PY_LIST_MAX = PY_SSIZE_T_MAX / 8` from CPython's list-allocation guard. Proof
layers, not the transcription, establish that intermediate values remain
valid. The one narrower expression in this roadmap is `merge_init`'s
`(1 << mr_e) - 1`: the unsuffixed C literal gives the expression type `int`,
and the selected v1 platform fixes that type at 32 bits. The transcription
therefore evaluates it in `BitVec 32` and widens its bit pattern into the
64-bit `Py_ssize_t` field. The selected behavior for
signed shifts outside ISO C's defined range is part of the explicit modeling
boundary, not a compiler-refinement claim.

## Depends on

No roadmap prerequisites.

## Sources

- [Modeling boundary](../../sources/toplevel-theorems.md#explicit-scope-boundary)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
- [Verbatim CPython list allocation guard](../../sources/listobject-excerpts.md#list-resize)
- [Sorting constants and `MergeState`](../../sources/listobject-excerpts.md#merge-state)
