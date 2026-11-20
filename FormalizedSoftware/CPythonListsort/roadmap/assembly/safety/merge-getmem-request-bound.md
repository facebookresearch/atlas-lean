---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeGetmem_callsite_request_bound
---

# `merge_getmem` call-site request bound

Let `pre` be the state in which `merge_at` selects two adjacent pending runs,
and let `call` be the later state at the `merge_getmem` call after stack update
and gallop trimming. From `PendingLayout pre scanned` and
`pre.listlen.toNat ≤ PY_LIST_MAX`, prove that the temporary-storage request
cannot trip `merge_getmem`'s allocation guard. State explicitly that this
control-flow segment preserves the fields relevant to the guard:
`call.listlen = pre.listlen`, `call.a.hasValues = pre.a.hasValues`, and
`call.alloced = pre.alloced`.

Let the two adjacent pending runs selected by `merge_at` have original lengths
`na₀` and `nb₀`, and let the post-gallop positive lengths be `na` and `nb`.
The proof must derive, rather than assume as an unrelated local fact, the full
run-length chain

`na.toNat + nb.toNat ≤ na₀.toNat + nb₀.toNat ≤ scanned ≤ pre.listlen.toNat`.

The second inequality comes from `PendingLayout`: pending runs tile the scanned
prefix without gaps, so every adjacent pair lies inside that prefix, which is
itself bounded by `listlen`. The first comes from gallop trimming only
decreasing the selected run lengths.

For the source dispatch

- `need = na` when `na ≤ nb` (`merge_lo`), and
- `need = nb` when `nb < na` (`merge_hi`),

prove the exact arithmetic chain

`need.toNat ≤ (na.toNat + nb.toNat) / 2 ≤ pre.listlen.toNat / 2`.

Then split on the retained values mode and expose the selected-platform
constants, rather than hiding them behind a qualitative allocation claim:

- keyed (`hasValues = true`, multiplier `2`):
  `mergeGetmemAllocationLimit call.a =
    PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 = 2^59 - 1`;
- unkeyed (`hasValues = false`, multiplier `1`):
  `mergeGetmemAllocationLimit call.a =
    PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES = 2^60 - 1`.

Conclude
`need.toNat ≤ mergeGetmemAllocationLimit call.a` and therefore
`(mergeGetmem call need).outcome ≠ .guardRejected`. The keyed fencepost is
machine-pinned by `mergeGetmem_keyed_boundary_regression`: with the growth path
forced, `need = 2^59 - 1` grows and `need = 2^59` is rejected
(`Code/Transcription/MergeMemory.lean:202`).

The Lean transcription exposes the actual post-trimming continuation through
`prepareMergeAt?`, retaining the selected runs and both concrete gallop
equations.  The proof applies `gallopRight_safe` and `gallopLeft_safe` to those
equations to obtain the trim bounds; it does not derive them from the model's
defensive out-of-range rejection checks.  Concrete regressions reach both the
`merge_lo` and `merge_hi` continuations, so the call-site contract is not
vacuous.

## Depends on

- [Pending-run layout invariant](../../policy/pending-layout.md)
- [Finite-width implementation model](../../transcription/word-model.md)
- [The `merge_getmem` transcription](../../transcription/merge-getmem.md)
- [The `merge_at` transcription](../../transcription/merge-at.md)

## Proof depends on

- [`gallop_left` safety](gallop-left-safe.md)
- [`gallop_right` safety](gallop-right-safe.md)

## Human arithmetic review

Check that the adjacent-run span is extracted from `PendingLayout`, trimming
is monotone, the guard-relevant fields agree between `pre` and `call`, `need`
is the smaller remaining run, natural-number division is rounded down, pointer
size is exactly `8`, and keyed mode uses the exact multiplier `2`. In
particular, check both sides of the `2^59 - 1` fencepost.

## Sources

- [Verbatim `merge_init` half-list explanation](../../../sources/listobject-excerpts.md#merge-init)
- [Verbatim `merge_getmem`](../../../sources/listobject-excerpts.md#merge-getmem)
- [Verbatim `merge_lo`](../../../sources/listobject-excerpts.md#merge-lo)
- [Verbatim `merge_hi`](../../../sources/listobject-excerpts.md#merge-hi)
- [Verbatim `merge_at`](../../../sources/listobject-excerpts.md#merge-at)
- [Selected platform and input domain](../../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
