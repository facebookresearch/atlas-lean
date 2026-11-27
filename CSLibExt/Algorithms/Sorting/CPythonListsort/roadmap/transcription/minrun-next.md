---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.minrunNext
---

# `minrun_next`

Transcribe the state transition that adds `listlen` to `mr_current`, returns
the arithmetic right-shifted quotient, and masks `mr_current` down to the
residual. The C assertion against overflow is represented as a trace flag;
proving that it remains true belongs to bit-level equivalence and safety.

## Depends on

- [merge_init minrun initialization](merge-init-minrun.md)

## Human transcription review

Compare the operation order carefully: addition precedes the returned shift,
and the mask updates the stored state only after the result is computed.

## Sources

- [Verbatim `minrun_next`](../../sources/listobject-excerpts.md#minrun-next)
- [CPython integer generator](../../sources/listsort.md#computing-minrun)
