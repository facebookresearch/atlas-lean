---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mirrorListSortScan
---

# Policy and complete scan commute with origin relabeling

The policy and scan layer retains comparator observations and all control-flow
choices while mirroring only carried origins.  The complete `mergeAt?` result
is consumed by `mirrorFoundNewRun`
(`Code/Correctness/OriginRelabelScan.lean:778`), then by
`mirrorMergeForceCollapse`
(`Code/Correctness/OriginRelabelScan.lean:898`).  Cleanup and the
final reversal branch commute through `mirrorFinishListSort`
(`Code/Correctness/OriginRelabelScan.lean:913`).

`mirrorListSortScan` packages the entire recursive evaluator equation.  For
any fuel, scan position, remaining length, reverse flag, and input extent,
running the mirrored state equals mapping `mirrorListSortImplResult` over the
unmirrored `listSortScan?` result.  Its only semantic premise is the explicit
comparator binding; it assumes no order law and no future correctness result
(`Code/Correctness/OriginRelabelScan.lean:1253`).

## Depends on

- [Origin-relabel equivariance support](origin-relabel-equivariance.md)
- [list_sort_impl](../../../transcription/list-sort-impl.md)

## Proof depends on

- [Merge evaluators commute with origin relabeling](merge-origin-equivariance.md)
- [`found_new_run` transcription](../../../transcription/found-new-run.md)
- [`merge_force_collapse` transcription](../../../transcription/merge-force-collapse.md)

## Sources

- [Verbatim `found_new_run`](../../../../sources/listobject-excerpts.md#found-new-run)
- [Verbatim `merge_force_collapse`](../../../../sources/listobject-excerpts.md#merge-force-collapse)
- [Verbatim `list_sort_impl`](../../../../sources/listobject-excerpts.md#list-sort-impl)
