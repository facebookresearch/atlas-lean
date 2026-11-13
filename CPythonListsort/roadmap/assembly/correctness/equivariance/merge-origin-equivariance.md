---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mirrorMergeAt
---

# Merge evaluators commute with origin relabeling

Origin labels are ghost data for comparison, but the complete merge machines
still have to move those labels and their optional payloads exactly with their
entries.  The raw `merge_lo` and `merge_hi` evaluators therefore commute with
the total origin mirror under only the explicit comparator-binding premise:
executing after mirroring is exactly `Option.map` of the corresponding mirrored
result.  These are theorem-pinned by `mirrorMergeLo` and `mirrorMergeHi`
(`Code/Correctness/OriginRelabelMerges.lean:1226` and
`Code/Correctness/OriginRelabelMerges.lean:2369`).

The selected-continuation theorem composes both directions, including the
already-finished branch
(`Code/Correctness/OriginRelabelScan.lean:518`).  The public node
closes at `mirrorMergeAt`: the complete raw `mergeAt?` call commutes with
mirroring, with no order-law or semantic sortedness premise
(`Code/Correctness/OriginRelabelScan.lean:580`).  Thus reverse-scan
transport consumes one explicit merge-level result rather than silently
depending on thousands of lines of unrepresented support.

## Depends on

- [Origin-relabel equivariance support](origin-relabel-equivariance.md)
- [`merge_at` transcription](../../../transcription/merge-at.md)

## Proof depends on

- [`merge_lo` transcription](../../../transcription/merge-lo.md)
- [`merge_hi` transcription](../../../transcription/merge-hi.md)

## Sources

- [Verbatim `merge_lo`](../../../../sources/listobject-excerpts.md#merge-lo)
- [Verbatim `merge_hi`](../../../../sources/listobject-excerpts.md#merge-hi)
- [Verbatim `merge_at`](../../../../sources/listobject-excerpts.md#merge-at)
