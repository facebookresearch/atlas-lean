---
declaration: structure
origin: bridged
statement: formalized
lean: CPythonListsort.AccessTrace
---

# Array-access, push-depth, and merge-memory trace model

Define the compositional trace carrier and the typed instrumentation interface
used to instrument the snapshot model without changing control flow. The
carrier records a fuel-exhaustion flag, every ordinary indexed read/write
attempt, ordered post-push pending-stack depths, and ordered raw merge-memory
boundary observations. Each ordinary access event identifies its region—input
keys, synchronized values, temporary merge storage, or an indexed access to the
current pending-run array—and records that region's extent. Define
`allAccessesInBounds` by checking the signed event index against its recorded
extent. Define `stackDepthMax` as the maximum of all recorded post-push depths,
with default zero when there were no pushes.

These carrier facts are definitional: the raw snapshot, call, and event types
are at `Code/Assembly/AccessTrace.lean:90`,
`Code/Assembly/AccessTrace.lean:142`, and
`Code/Assembly/AccessTrace.lean:163`; the four-channel `AccessTrace`
is at `Code/Assembly/AccessTrace.lean:174`, and chronological
composition is at `Code/Assembly/AccessTrace.lean:191`.

The merge-memory channel is deliberately non-validating. A
`MergeMemorySnapshot` type-erases the actual backing tag, mode bit, logical cell
count, signed `alloced`, physical slot count, and the per-entry presence of a
synchronized main-array value. A `MergeMemoryCallEvent` retains the merge
direction, requested and selected run lengths, source lengths, list length,
`merge_getmem` outcome, and the snapshots before allocation, at any intermediate
free, after allocation, and after the directional merge. `MergeMemoryEvent`
adds initial and final-cleanup boundaries. None of these records contains a
trusted Boolean claiming that an invariant holds. Function-specific traced
evaluators own the actual event insertion; the
[event-validity support node](merge-memory-event-validity.md) owns semantic
validation and continuity predicates; and the
[top-level lifecycle node](merge-memory-lifecycle.md) proves that the real
assembled execution inhabits those predicates.

Every temporary-storage payload read or write also records the backing state
observed at the attempted access. Define a separate predicate asserting that
such an event never has `backing = .released`. Reads of the mode and capacity
metadata (`hasValues` and `alloced`) are not payload-access events. Record
attempted payload accesses even if another safety predicate will later reject
them, so storage liveness is proved rather than filtered by instrumentation.
The temporary-payload wrappers derive both backing and extent from the actual
`TempStorage` at the attempt; callers may not supply those labels as trusted
proof data.

The pending push itself remains the total unbounded operation from
`list_sort_impl`; it is not a failed ordinary access when it extends the Lean
array. Do not add a capacity check, a refusal-to-mutate branch, or an
assertion-failure event. A forced push at depth 64 therefore records 65. The
separate theorem `stackDepthMax ≤ 61 < MAX_MERGE_PENDING` establishes that no
admitted execution attempts the write that would exceed CPython's fixed array.
The first claim is pinned by `forcedPushAtCapacity_records65` at
`Code/Assembly/AccessTrace.lean:979`; the admitted-execution bound is
pinned by `listsort_safe` at
`Code/Assembly/ListSortSafety.lean:14`.

Trace composition preserves chronological order, disjoins fuel exhaustion,
takes the exact maximum of component push depths, appends merge-memory events,
and distributes the bounds and liveness predicates. Prepending or appending a
merge-memory event preserves the evaluator result, ordinary-access channel,
push-depth channel, and fuel flag. Every typed primitive has an erasure law
showing that forgetting its trace recovers the corresponding uninstrumented
operation.

The event-insertion noninterference facts are theorem-pinned rather than
assumed. For prepending, result, erasure, ordinary accesses, push depths, fuel,
and `stackDepthMax` are at
`Code/Assembly/AccessTrace.lean:413`, `:425`, `:450`, `:463`, `:499`,
and `:552`. The corresponding append theorems are at lines 419, 431, 456, 470,
506, and 560. For success-conditional call insertion, the same six channels
are pinned at lines 437, 444, 514, 522, 530, and 568.
The common theorem that event-free helpers remain event-free through `bind` is
`memoryEvents_bind_eq_nil` at
`Code/Assembly/AccessTrace.lean:599`.

This node provides the carrier and honest primitive interface, not a decorative
empty wrapper around `list_sort_impl`. Each function-specific safety node owns
its traced evaluator and an exact erasure theorem back to the reviewed
transcription. The [fuel-adequacy node](termination.md) assembles those local
evaluators into raw `listSortImplTraced?`, then exposes the validated public
`listSortTraced?` wrapper; the local-bounds and top-level safety theorems
consume that produced public trace.

## Depends on

- [list_sort_impl](../../transcription/list-sort-impl.md)

## Sources

- [Safety theorem contract](../../../sources/toplevel-theorems.md#comparator-independent-safety)
