---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.foundNewRun?
---

# `found_new_run`

Transcribe the explicit no-op branch for an empty pending stack. Otherwise,
calculate the top run's power, repeatedly merge while the preceding stored
power is greater, and then store the new power. Comparator behavior is
irrelevant to this control decision.

## Depends on

- [MergeState and pending runs](merge-state.md)
- [powerloop](powerloop.md)
- [merge_at](merge-at.md)

## Sources

- [Verbatim `found_new_run`](../../sources/listobject-excerpts.md#found-new-run)
- [CPython merge pattern](../../sources/listsort.md#the-merge-pattern)
