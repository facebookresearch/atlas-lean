---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listSortImplTraced_tempPayloadAccessesLive
---

# Temporary-storage liveness

For the actual top-level traced evaluator assembled by the fuel-adequacy node,
prove that every valid raw execution satisfies
`execution.trace.tempPayloadAccessesLive`. The raw theorem assumes
`input.entries.size ≤ PY_LIST_MAX` and
`SortSlice.ValuesModeInvariant hasKeyfunc input`; the public corollary is stated
for `listSortTraced?` over `ListSortInput` and has no free representation-mode
premise. This is a trace-level result: every recorded temporary payload read or
write observed inline or heap backing, never `.released`. Metadata reads of
`hasValues` and `alloced` are not temporary payload events.

Derive the result from the real top-level control-flow composition. The
fuel-adequacy execution certificate establishes `TempStorage.Live` at
`initialMergeState`, carries it through `merge_at`, `found_new_run`, and final
collapse, and supplies it to each local merge-safety theorem. Those local
theorems both consume and return liveness and prove their own traced temporary
accesses live. `merge_freemem` on the exit path occurs only after all merge
operations have finished and emits no payload access. The transient free on a
successful-growth `merge_getmem` path is followed immediately by fresh live
heap backing before the merge performs a payload operation. The version-one
abstraction still excludes allocator failure.

This theorem therefore comes after the top-level traced evaluator. It does not
supply a premise retroactively to the local merge theorems: the top-level
induction discharges each local live-input premise from the preceding active
state, and this node projects the resulting whole-trace property.

## Depends on

- [Array-access and push-depth trace model](access-trace.md)
- [The `list_sort_impl` transcription](../../transcription/list-sort-impl.md)
- [`list_sort_impl` fuel adequacy](termination.md)

## Sources

- [Verbatim `merge_freemem`](../../../sources/listobject-excerpts.md#merge-freemem)
- [Verbatim `merge_getmem`](../../../sources/listobject-excerpts.md#merge-getmem)
- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
