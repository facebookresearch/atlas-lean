---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.readyToPush_stack_depth_bound
---

# `MAX_MERGE_PENDING` depth bound

From `ReadyToPush`, prove that every current pending run is powered and their
strictly increasing powers lie in `1 .. 60`, so the current depth is at most
60. The modeled push then executes unconditionally on the unbounded Lean array,
and its exact resulting depth is the previous depth plus one, hence at most
`61 < MAX_MERGE_PENDING = 64`. The one new unpowered top run is excluded from
the powered prefix until the following `found_new_run` call; its stored power
field is unconstrained and ignored. The inequality is
a proved property of the resulting state—not a precondition that enables the
push—and also implies that the corresponding release-build C write is within
the fixed pending array. The proof is a finite pigeonhole argument and contains
no comparator assumption or modeled debug-assertion event.

## Depends on

- [Powered-prefix invariant](stack-powers.md)
- [list_sort_impl](../transcription/list-sort-impl.md)

## Proof depends on

- [Power range bound](power-range.md)

## Sources

- [Verbatim stack-size constant](../../sources/listobject-excerpts.md#merge-state)
- [CPython stack discussion](../../sources/listsort.md#the-merge-pattern)
