---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeAt_safe
---

# `merge_at` safety

For a valid pending layout, the platform size premise
`state.listlen.toNat ≤ PY_LIST_MAX`, and either allowed stack index, prove that
`merge_at` terminates, indexes the pending stack safely, performs in-bounds
gallop trimming, and invokes the correctly oriented safe merge loop. The result
holds for an arbitrary total Boolean comparator. Treat every state before final
top-level cleanup as active: require both
`TempStorageInv state.a state.alloced` and `state.a.Live` at entry, and return
both facts for the result state. Early trimming returns leave temporary storage
unchanged, while `merge_lo` and `merge_hi` supply invariant and liveness
preservation on the two delegated branches. Thus the active-state premise used
by a merge call is supplied by the surrounding execution induction, and the
postcondition is strong enough to supply the next call; it is not deferred to a
later global liveness theorem.

Also require `SortSlice.ValuesModeInvariant state.a.hasValues state.data` at
entry and return the same relation for the post-merge state; gallop trimming is
read-only with respect to payload mode, while `merge_lo` and `merge_hi` supply
the two preservation branches. Return the independent frame equation
`result.state.a.hasValues = state.a.hasValues`. Do not try to recover that
Boolean equality from `ValuesModeInvariant`: on an empty slice the invariant
is vacuous and cannot distinguish the two modes.

Export a reusable stable frame for `listlen`, `basekeys`, data-array extent,
`a.hasValues`, `key_compare`, `mr_current`, `mr_e`, and `mr_mask`. The
`found_new_run`, collapse, and top-level scan proofs consume this frame to
transport their size bound, comparator, and adaptive-minrun state across each
delegated merge. Exclude pending contents, data contents, temporary
backing/cells, `alloced`, and `min_gallop`, all of which may legitimately
change.

Define the traced `merge_at` evaluator here and prove exact erasure to
`mergeAt?`. Record the C-level indexed pending reads and writes in source order:
the combined-run write at `i`, plus the `i+2` read and `i+1` write on the
third-last slide path. The logical active-array shrink is not itself an
ordinary indexed access event. Its postcondition also returns
`execution.trace.tempPayloadAccessesLive`, composing the vacuous main-only
trimming trace with the selected merge direction's non-vacuous temporary trace.

The same public post now exports the merge-memory obligations needed by the
top-level lifecycle: every emitted event is `Valid`, only directional-call
events occur, the initialized physical bound makes every call event `Bounded`,
and the trace is a continuous `MergeMemorySegment` from the caller snapshot to
the result snapshot. These fields are stated at
`Code/Assembly/MergeAtSafety.lean:1406`,
`Code/Assembly/MergeAtSafety.lean:1409`,
`Code/Assembly/MergeAtSafety.lean:1412`, and
`Code/Assembly/MergeAtSafety.lean:1422`; the final physical-bound
transport is at `Code/Assembly/MergeAtSafety.lean:1433`. Exact
cardinality is also public: each admitted call emits either `[]` or one
singleton directional-call event
(`Code/Assembly/MergeAtSafety.lean:1417`). All fields are produced
by the existing `mergeAt_safe` theorem at
`Code/Assembly/MergeAtSafety.lean:1838`; no new caller premise was
added.

## Depends on

- [Array-access trace model](access-trace.md)
- [Merge-memory event validity and continuous-segment support](merge-memory-event-validity.md)
- [Pending-run layout invariant](../../policy/pending-layout.md)
- [merge_at](../../transcription/merge-at.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [sortslice primitive safety](sortslice-safe.md)

## Proof depends on

- [gallop_left safety](gallop-left-safe.md)
- [gallop_right safety](gallop-right-safe.md)
- [merge_lo safety](merge-lo-safe.md)
- [merge_hi safety](merge-hi-safe.md)
- [merge_at preserves pending layout](../../policy/merge-at-preservation.md)

## Sources

- [Verbatim `merge_at`](../../../sources/listobject-excerpts.md#merge-at)
