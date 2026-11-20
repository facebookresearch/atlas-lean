---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.pushPendingRun_preserves_policy
---

# Pushing the new run restores the steady-state invariant

Given `ReadyToPush state scanned newRun`, evaluate the unconditional
`Array.push` of the new run and prove the exact post-state facts
`pending.toList = state.pending.toList ++ [newRun]`,
`PendingLayout pushed (scanned + newRun.len.toNat)`, and
`PoweredPrefix pushed`. The exact-label
part is carried without recomputation from `ReadyToPush`'s virtual list
`state.pending.toList ++ [newRun]`, which is exactly the pushed array's list.
Before the push the current depth is at most 60; its exact resulting size is
one larger, so the single new unpowered top run makes the depth at most
`61 < MAX_MERGE_PENDING = 64`. The new top power is deliberately unconstrained
because C does not assign it until the following `found_new_run` call.

The operation itself has no invariant or capacity precondition and always
mutates: when called directly on an artificial 64-entry state, it produces 65
entries, and the trace layer records post-push depth 65. `ReadyToPush` limits
only the preservation theorem's domain; it must not be used to implement a
refusal branch or an assertion-failure event.

## Depends on

- [Powered-prefix invariant](stack-powers.md)
- [list_sort_impl](../transcription/list-sort-impl.md)

## Proof depends on

- [MAX_MERGE_PENDING depth bound](stack-depth.md)

## Sources

- [Verbatim `found_new_run`](../../sources/listobject-excerpts.md#found-new-run)
- [Verbatim `list_sort_impl`](../../sources/listobject-excerpts.md#list-sort-impl)
