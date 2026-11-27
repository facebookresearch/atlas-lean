---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.mergeLo?
---

# `merge_lo`

Transcribe the left-to-right stable merge used when the left run is shorter,
including ordinary and galloping modes, `min_gallop` adjustment, and final
copy cases.

The review-sensitive control flow is part of this transcription:

- Straight mode tests `B[0] < A[0]`. A true result copies B, increments
  `bcount`, and resets `acount`; a false result, including equality, copies A,
  increments `acount`, and resets `bcount`. Thus equal left-run entries remain
  before equal right-run entries.
- Galloping first calls `gallop_right(B[0], A, na, 0)`, copies that A prefix,
  and then calls `gallop_left(A[0], B, nb, 0)`. Preserve the source's
  `na == 0` success branch after the first gallop: the v1 comparator is total
  but need not be consistent, so a gallop may consume the entire run.
- A-to-temp, temp-to-data, and final A-remainder blocks have distinct-store
  `memcpy` semantics. B blocks moved within the main data, including `CopyB`,
  use overlap-safe `memmove` semantics.
- CPython's `Succeed` and comparator-error `Fail` labels share the final
  A-remainder copyback. The v1 model retains that copy on successful exits but
  deliberately omits the comparator-error jump and negative result because
  `BoolComparator` cannot raise or return an error code. This is a modeling
  delta, not a claim that the C `Fail` path is unreachable in CPython.

The transcription exports an exact classification of its three
`memcpy`-class sites: the initial main-to-temporary copy and the
galloping/final temporary-to-main copies.  The
[call-site provenance theorem](../assembly/safety/merge-memcpy-provenance.md)
proves that every classified site has distinct backing.
The recursive bulk-copy executors themselves require the tag and its exact
backing-direction proof; there is no untagged lower bulk helper.

## Depends on

- [MergeState and pending runs](merge-state.md)
- [gallop_left](gallop-left.md)
- [gallop_right](gallop-right.md)
- [merge_getmem](merge-getmem.md)

## Sources

- [Verbatim `merge_lo`](../../sources/listobject-excerpts.md#merge-lo)
- [CPython merge algorithms](../../sources/listsort.md#merge-algorithms)
