---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.listSortImpl?
---

# `list_sort_impl`

Assemble the snapshot-model control flow: optional reversal, natural-run scan,
adaptive minrun extension, policy merges, pending-run push, final collapse, and
result reversal. Key-function setup, exception propagation, mutation detection,
and interpreter bookkeeping are recorded but excluded from v1 behavior.

Expose `initialMergeState` publicly so the assembly layer can connect a
validated input to the initialized machine state. Its simp lemmas
`initialMergeState_data` and `initialMergeState_temp_hasValues` state exactly
that the main data is the supplied slice and the temporary-storage mode equals
the raw `hasKeyfunc` argument. These are projection facts, not validation: raw
`listSortImpl?` deliberately continues to accept a separate Boolean and
`SortSlice`; the proof-carrying `ListSortInput`/`listSort?` boundary is owned by
the safety layer.

Implement the pending-run write as an unconditional, total
`state.pending.push newRun`. It does not inspect `MAX_MERGE_PENDING`, refuse a
mutation at depth 64, or model the source `assert` as a failure branch. Thus a
direct call from an artificial 64-entry state really produces 65 entries; the
instrumented evaluator records that resulting depth, and the safety proof—not
the definition—must show that admitted top-level executions never do this.

## Depends on

- [merge_init minrun initialization](merge-init-minrun.md)
- [`merge_init` temporary-storage setup](merge-init-storage.md)
- [MergeState and pending runs](merge-state.md)
- [sortslice model and movement primitives](sortslice-primitives.md)
- [minrun_next](minrun-next.md)
- [count_run](count-run.md)
- [binarysort](binarysort.md)
- [found_new_run](found-new-run.md)
- [merge_force_collapse](merge-force-collapse.md)
- [merge_freemem](merge-freemem.md)
- [Slice reversal](reverse-slice.md)

## Sources

- [Verbatim `list_sort_impl`](../../sources/listobject-excerpts.md#list-sort-impl)
- [Modeling boundary](../../sources/toplevel-theorems.md#explicit-scope-boundary)
