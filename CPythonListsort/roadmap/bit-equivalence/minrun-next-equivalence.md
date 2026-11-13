---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.minrunNext_eq_spec
---

# `minrun_next` conditional quotient-remainder equivalence

Assuming `mr_e < 32`, an exact mathematical low-bit mask, and representable
addition, prove that the emitted size is
`(mr_current + listlen) / 2^mr_e` and the stored residual is
`(mr_current + listlen) % 2^mr_e`. These are the literal premises of
`minrunNext_eq_spec` at `Code/Equivalence/Minrun.lean:183`.
Without the exponent and exact-mask premises, the quotient statement for the
current call may still hold but the mathematical-remainder statement does
not describe the next stored state once the 32-bit mask truncates.

## Depends on

- [minrun_next](../transcription/minrun-next.md)

## Sources

- [CPython integer generator](../../sources/listsort.md#computing-minrun)
- [Verbatim `minrun_next`](../../sources/listobject-excerpts.md#minrun-next)
