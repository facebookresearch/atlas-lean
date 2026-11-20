---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.foundNewRun_safe
---

# `found_new_run` safety

Given a stack satisfying the steady-state policy invariant and an adjacent
nonempty new run on the selected `listlen.toNat ≤ PY_LIST_MAX` domain, prove
that `found_new_run` returns `some result` with return code zero and
`fuelExhausted = false`. The policy-preservation theorem then supplies
`ReadyToPush result.state scanned newRun`; it does not assume this successful
result exists. The empty-stack branch performs no pending access; the nonempty
branch reads and writes only live entries, calls `powerloop` on signed-safe
arguments, and calls `merge_at` only at its allowed top index. No comparator
law is assumed. Its contract also takes
`SortSlice.ValuesModeInvariant state.a.hasValues state.data` and returns it:
the empty-stack and power-write branches leave data untouched, and every
policy-triggered merge uses `merge_at`'s preservation result. Return
`result.state.a.hasValues = state.a.hasValues` separately as well, composing
the frame equation across every merge. This equality may not be inferred from
the values-mode invariant because the data slice can be empty.

The entry state is also an active temporary-storage state: require
`TempStorageInv state.a state.alloced` and `state.a.Live`, carry both through
every recursive iteration, and return both for `result.state`. Empty-stack and
power-only branches frame the storage directly; a merge iteration obtains the
two postconditions from `merge_at`. This makes `found_new_run` a genuine
inductive preservation step for the top-level scan rather than assuming at a
higher layer that the whole execution is already live.

Export the helper frame needed by the next scan iteration: preserve `listlen`,
`basekeys`, the data-array extent, `a.hasValues`, `key_compare`, `mr_current`,
`mr_e`, and `mr_mask`. Do not claim that `min_gallop`, pending runs, temporary
backing/cells, or `alloced` are unchanged: delegated merges may legitimately
change those fields. In particular, preserving `listlen` and the three `mr_*`
fields keeps the next `minrunNext state.minrunState` call tied to the actual
top-level state rather than an implicit C frame assumption.

Define the traced `found_new_run` evaluator here and, for every source-admitted
call covered by this node, export exact erasure to `foundNewRun?`, including
its pending reads, top-power write, and delegated merge traces. Independently
pin both explicit fuel-exhaustion branches with structural equations or closed
regressions, so those modeled failure paths remain checked even though the
successful safety theorem proves that neither is taken. Compose
`execution.trace.tempPayloadAccessesLive` across each delegated `merge_at`
trace; pending and powerloop-only events satisfy it vacuously.
The empty-stack branch records no access. A nonempty call first records the
current-top read; every loop test with at least two runs records the
second-last-run read; the stopping branch records the final top-power write;
and a taken merge branch appends the complete `merge_at` trace before the next
test. The helper never records a pending push because the caller owns that
operation.

Keep the invalid uninitialized-power arm nonvacuous in the model:
`foundNewRunLoopTraced_unpowered_preceding_failure` and its end-to-end companion
`foundNewRunTraced_unpowered_prefix_failure` exhibit a concrete two-run state
that violates `PoweredPrefix`, reaches the uninitialized preceding-power arm,
returns `none` after the top and second-last pending reads, and records no
fuel-exhaustion marker or push. The two theorem pins are at
`Code/Assembly/FoundNewRunSafety.lean:1359` and
`Code/Assembly/FoundNewRunSafety.lean:1378`.

For lifecycle composition, the public `FoundNewRunSafetyPost` additionally
exports semantic validity and directional-only classification for every memory
event, physical boundedness from the incoming initialized bound, preservation
of that bound to the result state, and a continuous memory segment. The exact
fields are at `Code/Assembly/FoundNewRunSafety.lean:710`,
`Code/Assembly/FoundNewRunSafety.lean:713`,
`Code/Assembly/FoundNewRunSafety.lean:715`,
`Code/Assembly/FoundNewRunSafety.lean:718`, and
`Code/Assembly/FoundNewRunSafety.lean:721`; they are produced without
additional premises by
the existing `foundNewRun_safe` theorem at
`Code/Assembly/FoundNewRunSafety.lean:979`. In the proof body, the
recursive equation explicitly concatenates the literal `merge_at` event list
with the recursive event list at
`Code/Assembly/FoundNewRunSafety.lean:467`; this line explains the
construction but is not a separate pinning theorem. The exported
`memorySegment` field above is the theorem-level consumer boundary.

## Depends on

- [Array-access trace model](access-trace.md)
- [Merge-memory event validity and continuous-segment support](merge-memory-event-validity.md)
- [Pending-run layout invariant](../../policy/pending-layout.md)
- [Powered-prefix invariant](../../policy/stack-powers.md)
- [found_new_run](../../transcription/found-new-run.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [sortslice primitive safety](sortslice-safe.md)
- [merge_at safety](merge-at-safe.md)

## Proof depends on

- [powerloop trace safety](../../bit-equivalence/powerloop-trace-safety.md)
- [Boundary-power geometry for three consecutive runs](../../policy/boundary-power-geometry.md)
- [Top merge preserves the powered prefix](../../policy/merge-top-power-preservation.md)
- [found_new_run preserves policy invariants](../../policy/found-new-run-preservation.md)

## Sources

- [Verbatim `found_new_run`](../../../sources/listobject-excerpts.md#found-new-run)
