---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.gallopRight_safe
---

# `gallop_right` safety

For a valid slice and in-bounds hint, prove that the exponential and binary
search phases of `gallop_right` terminate, use signed-representable index
arithmetic, read only within the slice, and return an index at most its length.
No comparator law is assumed.

Define the traced `gallop_right` evaluator here and prove exact erasure to
`gallopRight?`. Its key-source interface distinguishes main-data probes from
temporary-storage probes, so a temporary gallop records the actual temporary
backing and physical logical-cell index rather than a materialized ghost slice.
The exported trace contract also states `pushDepths = []`; merge safety
therefore consumes a named no-push fact instead of re-reading the evaluator's
implementation.
For a temporary call, a bounded `AgreesWithSlice` relation connects those
direct reads to the reviewed materialized slice. The exported `tempRun?` cell
specification discharges that relation for the actual `merge_lo` call path.

## Depends on

- [Array-access trace model](access-trace.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [gallop_right](../../transcription/gallop-right.md)
- [merge_lo](../../transcription/merge-lo.md)

## Proof depends on

- [`gallop_left` safety](gallop-left-safe.md)

## Sources

- [Verbatim `gallop_right`](../../../sources/listobject-excerpts.md#gallop-right)
- [Verbatim `merge_lo`](../../../sources/listobject-excerpts.md#merge-lo)
