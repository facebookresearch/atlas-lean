# Implementation transcription

This chapter is the human-review boundary between the pinned C and Lean. Each
leaf introduces one C function or tightly coupled state transition and cites
the exact verified excerpt. These nodes make no correctness claims: a compiled
definition establishes only that the Lean artifact exists.

## Representation and movement

- [Finite-width implementation model](word-model.md)
- [Total Boolean comparator model](comparator-model.md)
- [`sortslice` model and movement primitives](sortslice-primitives.md)
- [`MergeState` and pending runs](merge-state.md)
- [Temporary-storage representation invariant](temp-storage-invariant.md)
- [Slice reversal](reverse-slice.md)

## Adaptive minrun

- [`merge_init` minrun initialization](merge-init-minrun.md)
- [`merge_init` temporary-storage setup](merge-init-storage.md)
- [`minrun_next`](minrun-next.md)

The `merge_init` mask is the chapter's deliberate mixed-width case: C's
unsuffixed `1` makes `(1 << mr_e) - 1` an `int` expression, and the selected v1
platform fixes `int` at 32 bits before the result is stored in a 64-bit field.
For signed shifts outside ISO C's defined range, the transcription records an
explicit bit-vector convention and the claim boundary does not pretend that
convention is portable compiler behavior.

## PowerSort policy transcription

- [`powerloop`](powerloop.md)
- [`found_new_run`](found-new-run.md)
- [`merge_force_collapse`](merge-force-collapse.md)

## Run formation

- [`count_run`](count-run.md)
- [`binarysort`](binarysort.md)

## Galloping and merging

- [`gallop_left`](gallop-left.md)
- [`gallop_right`](gallop-right.md)
- [`merge_freemem`](merge-freemem.md)
- [`merge_getmem`](merge-getmem.md)
- [`merge_lo`](merge-lo.md)
- [`merge_hi`](merge-hi.md)
- [`merge_at`](merge-at.md)

## Top-level control flow

- [`list_sort_impl`](list-sort-impl.md)

The v1 comparator is total and cannot raise. Allocation failure, comparator
specialization, list mutation, and interpreter bookkeeping are recorded as
explicit modeling deltas rather than silently transcribed.

The fixed C pending buffer is represented by an unbounded Lean `Array`.
Pending-run pushes always mutate, including a hypothetical 64-to-65 push, and
the instrumented evaluator records every resulting post-push depth. Capacity
safety is a downstream theorem rather than a guarded transition, and CPython's
debug assertion is not modeled as an event.
