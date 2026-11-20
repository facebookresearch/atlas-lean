---
declaration: abbrev
origin: bridged
statement: formalized
lean: CPythonListsort.BoolComparator
---

# Total Boolean comparator model

Define the version-one comparator as a pure total function
`α → α → Bool` and route every transcribed `IFLT(x, y)` test through it with
the same argument and call order. This deliberately omits CPython's negative
error return, specialization function pointers, and comparator side effects;
those deltas remain explicit rather than being confused with C behavior.

## Depends on

No roadmap prerequisites.

## Sources

- [Verbatim comparison dispatch](../../sources/listobject-excerpts.md#comparison-dispatch)
- [Version-one modeling boundary](../../sources/listobject-excerpts.md#version-one-modeling-boundary)
