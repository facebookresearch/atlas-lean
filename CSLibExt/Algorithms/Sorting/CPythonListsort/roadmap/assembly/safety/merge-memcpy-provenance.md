---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeMemcpyCallsiteProvenance
---

# Merge `memcpy` call-site provenance

Classify every `memcpy`-class bulk-movement site exported by the `merge_lo`
and `merge_hi` transcriptions.  For `merge_lo`, this covers the initial
main-to-temporary copy and the galloping/final temporary-to-main copies.  For
`merge_hi`, it covers the corresponding initial main-to-temporary copy and
galloping/final temporary-to-main copies.  Prove that every classified site
crosses the two backing regions, so its provenance is `distinctBacking` and it
discharges the `sortslice` `memcpy` admissibility gate.

Together with `sortslice_primitives_safe`, this proves both sides of the
call-site obligation: an overlapping same-backing request is rejected, while
every `memcpy` request that a merge can issue has distinct backing.  Thus the
merge safety proofs do not inherit C pointer separation as an unstated fact.

Enforce this in Lean rather than in CI: the recursive bulk-copy implementations
themselves take the classified call-site tag and an equality proof of the exact
main-to-temporary or temporary-to-main direction. There is no lower untagged
bulk `memcpy` helper for an evaluator call to invoke. The remaining one-cell
helpers in `merge_hi` are hardwired cross-store primitives; its temp-to-data
helper also implements ordinary `sortslice_copy`. Same-store movement remains
the separately modeled overlap-safe `memmove` path.

## Depends on

- [`sortslice` primitive safety](sortslice-safe.md)
- [The merge_lo transcription](../../transcription/merge-lo.md)
- [The merge_hi transcription](../../transcription/merge-hi.md)

## Review regression

The call-site classification is exact, not illustrative.  Every newly added
merge `memcpy` site must extend it and prove distinct backing.  A C comment,
private helper shape, or informal claim that the pointers differ does not
discharge this obligation without an exported Lean theorem and an explicit
roadmap dependency edge. The tagged argument must remain on the recursive bulk
implementation itself rather than on a wrapper around an untagged executor.

## Sources

- [Verbatim `sortslice` primitives](../../../sources/listobject-excerpts.md#sortslice-primitives)
- [Verbatim `merge_lo`](../../../sources/listobject-excerpts.md#merge-lo)
- [Verbatim `merge_hi`](../../../sources/listobject-excerpts.md#merge-hi)
