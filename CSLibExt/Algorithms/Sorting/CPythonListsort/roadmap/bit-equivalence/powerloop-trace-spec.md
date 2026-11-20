---
declaration: def
origin: bridged
statement: formalized
lean: CPythonListsort.PowerloopTraceSafe
---

# `powerloop` safety-trace specification

Define `PowerloopStepSafe` and `PowerloopTraceSafe`. At every visited
non-stopped state they record nonnegative signed operands, their required
ordering, and signed-safe doubles for the next transition. The recursive trace
predicate follows the transcribed step exactly and stops when the bounded loop
does.

## Depends on

- [powerloop](../transcription/powerloop.md)
- [Finite-width implementation model](../transcription/word-model.md)

## Sources

- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [CPython arithmetic-slack explanation](../../sources/listsort.md#the-merge-pattern)
