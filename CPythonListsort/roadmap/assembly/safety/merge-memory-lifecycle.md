---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listSortImpl_mergeMemory_lifecycle
---

# Trace-backed temporary-memory lifecycle witness

For an arbitrary Boolean comparator, reverse flag, storage mode, and raw
`SortSlice` satisfying only the platform size bound and the explicit
values-mode invariant, prove that the real `listSortImplTraced?` evaluator
returns a result whose own `trace.memoryEvents` satisfies the exact
`MergeMemoryLifecycle` predicate.

The unique projection theorem is
`listSortImpl_mergeMemory_lifecycle` at
`Code/Assembly/MergeMemorySafety.lean:22`. Its conclusion includes
both the actual result equation and the lifecycle over the concrete
`initialMergeState` and returned-state snapshots. It is projected from
`listSortImplTraced_safe`; this node therefore does not duplicate or replace
the termination evaluator.

The upstream support predicate `AccessTrace.MergeMemoryLifecycle`, defined at
`Code/Assembly/MergeMemoryLifecycle.lean:1023`, has the exact
source-order equation:

1. one `MergeMemoryEvent.initial` snapshot taken from the concrete
   `initialMergeState`;
2. zero or more real directional `MergeMemoryEvent.mergeCall` observations in
   call order, connected by `MergeMemoryCallChain`; and
3. one terminal `MergeMemoryEvent.cleanup` containing the concrete states
   immediately before and after the exit-path `merge_freemem`.

The semantic validity, bounds, and continuity vocabulary consumed by this
definition lives in the earlier
[merge-memory event validity support node](merge-memory-event-validity.md).
The lifecycle quantifies over the same call list appearing in the literal
trace equation and requires every call to be both `Valid` and `Bounded`, the
initializer to satisfy `ActiveCore`, and the final transition to satisfy
`CleanupValid`; no separately supplied history can omit a call or bridge a
state gap.

The chronology is theorem-pinned at each actual instrumentation boundary. An
admitted top-level execution has the concrete initializer as its head by
`listSortImplTraced_initial_event_head`
(`Code/Assembly/ListSortTrace.lean:409`). Each admitted `merge_at`
emits either no lifecycle event or exactly one directional-call event, and its
observed boundaries form one continuous segment; those are the public fields
at `Code/Assembly/MergeAtSafety.lean:1417` and `:1422`. Final cleanup
is appended from the actual pre-`mergeFreemem` state; the inactive and active
exact-event equations are at
`Code/Assembly/ListSortTrace.lean:176` and `:190`.

The helper-segment and terminal-tail composition theorems are at
`Code/Assembly/MergeMemoryLifecycle.lean:994` and `:1007`; the
initializer assembly theorem is at
`Code/Assembly/MergeMemoryLifecycle.lean:1040`. Adding the memory
channel does not alter existing results. For prepending, result, erasure,
ordinary accesses, push depths, fuel, and stack depth are pinned at
`Code/Assembly/AccessTrace.lean:413`, `:425`, `:450`, `:463`, `:499`,
and `:552`; the corresponding append pins are at lines 419, 431, 456, 470,
506, and 560. The success-conditional insertion used by directional calls has
the same six pins at lines 437, 444, 514, 522, 530, and 568.

## Depends on

- [Merge-memory event validity and continuous-segment support](merge-memory-event-validity.md)
- [`list_sort_impl`](../../transcription/list-sort-impl.md)
- [Array-access, push-depth, and merge-memory trace model](access-trace.md)

## Proof depends on

- [`list_sort_impl` fuel adequacy and actual traced evaluator](termination.md)

## Sources

- [Verbatim `merge_init`](../../../sources/listobject-excerpts.md#merge-init)
- [Verbatim `merge_freemem`](../../../sources/listobject-excerpts.md#merge-freemem)
- [Verbatim `merge_getmem`](../../../sources/listobject-excerpts.md#merge-getmem)
- [Verbatim `merge_at`](../../../sources/listobject-excerpts.md#merge-at)
- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
- [Modeling boundary](../../../sources/toplevel-theorems.md#explicit-scope-boundary)
