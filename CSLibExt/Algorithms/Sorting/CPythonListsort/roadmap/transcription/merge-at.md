---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.mergeAt?
---

# `merge_at`

Transcribe stack replacement, pre-merge gallop trimming, and selection of
`merge_lo` or `merge_hi` by remaining run lengths.

The Lean definition factors the stack-update and trimming prefix into
`prepareMergeAt?`.  Its merge continuations retain the exact selected runs,
call state, and both gallop results; `mergeAt?` immediately executes that
continuation.  This is an observational factoring of the same control flow,
used so downstream safety proofs can derive allocation requests from the real
call site instead of reconstructing implicit C facts.  Executable regressions
reach both directional continuations.

The third-last stack-slide witness `mergeAt_slide_regression` is one of the
compiler-checked leaves listed in the project-wide
[proof trust boundary](../README.md#proof-trust-boundary)
(`Code/Transcription/MergeAt.lean:484`). It is review evidence only
and has no Lean consumer; the smaller directional-preparation witnesses use
kernel `decide`.

## Depends on

- [MergeState and pending runs](merge-state.md)
- [sortslice model and movement primitives](sortslice-primitives.md)
- [gallop_left](gallop-left.md)
- [gallop_right](gallop-right.md)
- [merge_lo](merge-lo.md)
- [merge_hi](merge-hi.md)

## Sources

- [Verbatim `merge_at`](../../sources/listobject-excerpts.md#merge-at)
