# Comparator-independent safety

This section proves one safety theorem per transcribed function and then
composes them into top-level fuel-adequacy and access-bound results. Every node
holds for an arbitrary total Boolean comparator.

The trace-model node defines the carrier and typed primitive interface. Each
local-safety node adds the traced evaluator and exact erasure theorem for its
own transcribed function; fuel adequacy assembles those pieces into the single
top-level traced evaluator consumed by the final results. The merge-memory
event-validity node supplies the pre-`merge_at` semantic and continuity
vocabulary. After the scan proof assembles the real evaluator, the dedicated
lifecycle theorem projects its initialization/calls/cleanup witness, while the
aggregate theorem independently projects the broader storage-safety post from
the same kernel-checked top-level certificate.

The completed public boundary is `listSort_mergeMemory_safe`
(`Code/Assembly/MergeMemorySafety.lean:200`). Its raw counterpart is
`listSortImpl_mergeMemory_safe`
(`Code/Assembly/MergeMemorySafety.lean:159`). The unique exact
initial-to-calls-to-cleanup projection is
`listSortImpl_mergeMemory_lifecycle` at
`Code/Assembly/MergeMemorySafety.lean:22`.

Pending-stack storage is intentionally unbounded in the Lean model and every
push succeeds. The trace records each resulting post-push depth, and the final
theorem proves its maximum is at most 61 and that
`61 < MAX_MERGE_PENDING = 64`; no capacity guard or modeled debug assertion
makes that result true by construction. The forced depth-64 push is
theorem-pinned to record 65 at
`Code/Assembly/AccessTrace.lean:979`; the admitted top-level bound is
theorem-pinned by `listsort_safe` at
`Code/Assembly/ListSortSafety.lean:14`.

As a standing review rule, a source fact that is only implicit in C pointer
identity, control flow, or helper construction does not count as discharged.
Safety consumers must cite an exported Lean statement and carry an explicit
dependency edge; call-site classifications must be extended when new sites are
introduced. Reviewers must verify that edge in Autoform's rendered node
neighborhood rather than treating a prose link as graph evidence.

## Trace model

- [Array-access, push-depth, and merge-memory trace model](access-trace.md)

## Local safety

- [`sortslice` primitive safety](sortslice-safe.md)
- [Merge `memcpy` call-site provenance](merge-memcpy-provenance.md)
- [Slice-reversal safety](reverse-slice-safe.md)
- [`count_run` safety](count-run-safe.md)
- [`binarysort` safety](binarysort-safe.md)
- [`gallop_left` safety](gallop-left-safe.md)
- [`gallop_right` safety](gallop-right-safe.md)
- [`merge_init` establishes temporary-storage validity](merge-init-storage-valid.md)
- [`merge_freemem` preserves temporary-storage validity](merge-freemem-storage-valid.md)
- [`merge_getmem` call-site request bound](merge-getmem-request-bound.md)
- [`merge_getmem` establishes live temporary capacity](merge-getmem-storage-valid.md)
- [`merge_lo` safety](merge-lo-safe.md)
- [`merge_hi` safety](merge-hi-safe.md)
- [Merge-memory event validity and continuous-segment support](merge-memory-event-validity.md)
- [`merge_at` safety](merge-at-safe.md)
- [`found_new_run` safety](found-new-run-safe.md)
- [`merge_force_collapse` safety](merge-force-collapse-safe.md)

## Assembly

- [`list_sort_impl` fuel adequacy](termination.md)
- [Temporary-storage liveness](temp-storage-liveness.md)
- [Trace-backed temporary-memory lifecycle witness](merge-memory-lifecycle.md)
- [Temporary merge-memory safety](merge-memory-safe.md)
- [`list_sort_impl` access bounds](local-bounds.md)
- [`listsort_safe`](listsort-safe.md)
