---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.mergeHi?
---

# `merge_hi`

Transcribe the right-to-left stable merge used when the right run is shorter.
Keep its movement direction and equality behavior distinct from `merge_lo`.

The review-sensitive control flow is part of this transcription:

- Straight mode still tests `B[0] < A[0]`. A true result copies A backward,
  increments `acount`, and resets `bcount`; a false result, including equality,
  copies B backward, increments `bcount`, and resets `acount`. Writing the equal
  B entry into the higher destination slot is what leaves the equal A entry
  before it in final forward order.
- The first gallop calls `gallop_right(B[0], A, na, na - 1)` and converts its
  insertion index to the backward block length `na - k`. The second calls
  `gallop_left(A[0], B, nb, nb - 1)` and uses `nb - k`. Preserve the source's
  post-gallop `na == 0` and `nb == 0` success branches: a total comparator may
  still be inconsistent.
- A blocks moved within the main data, including `CopyA`, use overlap-safe
  `memmove` semantics. B-to-temp, temp-to-data, and final B-remainder blocks
  have distinct-store `memcpy` semantics.
- CPython's `Succeed` and comparator-error `Fail` labels share the final
  B-remainder copyback. The v1 model retains that copy on successful exits but
  deliberately omits the comparator-error jump and negative result because
  `BoolComparator` cannot raise or return an error code. This is a modeling
  delta, not a claim that the C `Fail` path is unreachable in CPython.

The transcription exports an exact classification of its three
`memcpy`-class sites: the initial main-to-temporary copy and the
galloping/final temporary-to-main copies.  The
[call-site provenance theorem](../assembly/safety/merge-memcpy-provenance.md)
proves that every classified site has distinct backing.
The recursive bulk-copy executors themselves require the tag and its exact
backing-direction proof. Untagged one-cell helpers remain only for the
hardwired cross-store `sortslice_copy` operations.

## Depends on

- [MergeState and pending runs](merge-state.md)
- [gallop_left](gallop-left.md)
- [gallop_right](gallop-right.md)
- [merge_getmem](merge-getmem.md)

## Sources

- [Verbatim `merge_hi`](../../sources/listobject-excerpts.md#merge-hi)
- [CPython merge algorithms](../../sources/listsort.md#merge-algorithms)
