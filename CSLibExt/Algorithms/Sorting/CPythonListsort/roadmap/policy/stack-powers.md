---
declaration: def
origin: bridged
statement: formalized
lean: CPythonListsort.PoweredPrefix
---

# Powered-prefix invariant

Define `PoweredPrefix`: only indices strictly below the newest pending run
carry computed node powers. For every adjacent pending pair `(left, right)`,
the stored power on `left` is exactly
`powerloop (left.base - basekeys) left.len right.len listlen`, using the
transcribed 64-bit operation. The condition is vacuous for empty and singleton
stacks; otherwise those exact powers are strictly increasing in C array order
and each lies in the concrete interval `1 .. 60`. Thus there are at most 60
powered runs; including the unique newest unpowered run gives depth at most
`61 < MAX_MERGE_PENDING = 64`.

Also define `ReadyToPush`, the state immediately before the caller pushes a
newly discovered adjacent run and, on a nonempty stack, after
`found_new_run`'s stop branch has called `setTopPower`. Every current pending
run then has a computed increasing power, and exact boundary labels hold on
the virtual list `state.pending.toList ++ [newRun]`; therefore the current top
is already labeled for its boundary with `newRun`. The new run itself is not
yet on the stack. This includes the initial empty stack, for which
`found_new_run` deliberately takes its no-op branch.

Do not require that virtual-list exactness during the collapse loop. Its
invariant is `PoweredPrefix` together with a separate ghost candidate `q` that
is the exact power between the current top and the prospective run. A top-pair
merge changes only the top run's length and carries its old physical `power`
field into the merged top. That field is stale and deliberately unconstrained
by `PoweredPrefix`, because only entries strictly below the newest pending run
are semantically powered. The stop branch overwrites it with `q`; only then
does `ReadyToPush` require `ExactBoundaryPowers` on
`state.pending.toList ++ [newRun]`. The prospective run's own stored `power`
field remains unconstrained because CPython's subsequent push writes only its
base and length, and no policy step reads that field before overwriting it.
Neither invariant contains a capacity guard: the subsequent push is a total
operation, and its depth bound is a theorem. The definitions record the
stack-local facts; preservation theorems separately take the top-level input
domain `listlen.toNat ≤ PY_LIST_MAX`, which is required by the proved
`powerloop` range theorem and by the proved boundary-geometry theorems.

## Depends on

- [Pending-run layout invariant](pending-layout.md)
- [MergeState and pending runs](../transcription/merge-state.md)
- [powerloop](../transcription/powerloop.md)
- [Finite-width implementation model](../transcription/word-model.md)

## Sources

- [CPython stack invariant](../../sources/listsort.md#the-merge-pattern)
- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [Verbatim `found_new_run`](../../sources/listobject-excerpts.md#found-new-run)
- [Verbatim `list_sort_impl`](../../sources/listobject-excerpts.md#list-sort-impl)
- [Verbatim list-allocation guard](../../sources/listobject-excerpts.md#list-resize)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
