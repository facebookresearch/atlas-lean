---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.powerloopTraced_eq_spec
---

# `powerloop` recurrence equivalence

Show that each finite-width transcription step agrees with the corresponding
arbitrary-precision recurrence whenever `a`, `b`, and `n` are nonnegative
signed values and the next subtraction or left shift stays below `2^63`. Lift
the result through the 64-step total loop, and prove that signed-representable
initial midpoint expressions are converted to the exact natural-number
midpoints rather than their wrapped residues. This theorem remains conditional
on an explicit safety trace; a downstream theorem constructs that trace from
valid adjacent runs and `n ≤ PY_LIST_MAX`.

## Depends on

- [powerloop](../transcription/powerloop.md)
- [Finite-width implementation model](../transcription/word-model.md)
- [Natural-number powerloop specification](powerloop-nat-spec.md)
- [powerloop safety-trace specification](powerloop-trace-spec.md)

## Sources

- [CPython quotient-bit explanation](../../sources/listsort.md#the-merge-pattern)
- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
