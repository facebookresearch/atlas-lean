---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.binarysort_safe
---

# `binarysort` safety

For `1 ≤ n ≤ MAX_MINRUN`, `ok ≤ n`, and
`SortSlice.RangeInBounds slice base n`, binary insertion returns successfully
for an arbitrary total Boolean comparator. Its public postcondition exports
both returned-result and trace non-exhaustion, no pending pushes, in-bounds
accesses, live temporary-payload accesses, exact erasure, preservation of
`SortSlice.ValuesModeInvariant state.a.hasValues`, preservation of the backing
array extent, and `RangeInBounds` for the returned slice. These are the
consumer fields needed by the top-level scan; no comparator ordering law is
assumed.

The node defines a genuine traced `binarysort` evaluator assembled from traced
`SortSlice` reads, writes, and backward moves. Erasure agrees with `binarysort?`
on the complete raw domain, including rejected assertion-domain inputs and
synthetic fuel paths. The search contract proves that interval width supplies
enough fuel and returns a position between its input endpoints; the outer loop
uses `n` fuel and proves that source-admitted calls cannot exhaust it.

Source-specific order is exposed separately. Every active search step reads
the arithmetic midpoint before the comparator-selected recursive branch, with
the call-site theorem also recording `right ≤ n ≤ MAX_MINRUN` and
`left + right ≤ 2 * MAX_MINRUN ≤ PY_SSIZE_T_MAX`, directly discharging the
C midpoint addition's signed no-overflow premise. The insertion geometry
theorem exposes the valid source/destination overlap ranges and pivot/insert
cells. Nonempty key and synchronized-value shifts start at the highest
source/destination pair; the values-mode insertion theorem orders the key
shift, key pivot write, value pivot read, value shift, and value pivot write.
One outer iteration orders the pivot read, complete search, complete insertion,
and recursive continuation.

Executable regressions cover singleton and unsorted-pair `ok = 0`
normalization, a leftmost two-cell shift, a rightmost insertion with zero shift
but retained pivot writes, and explicit no-values mode with no synchronized-
values events. A strict-comparator witness sorts tagged
`[1a, 1b, 2x, 1c]` to `[1a, 1b, 1c, 2x]`, so the comparator-false/right branch
and its stability-relevant shift are observable. Separate witnesses cover a
rejected assertion guard, retention of an attempted out-of-bounds read, and
concrete active zero-fuel search and outer-loop calls. The two general
zero-fuel theorems additionally keep those synthetic exhaustion arms
observable.

Version-one deliberately uses a pure total `BoolComparator`. CPython's active
`IFLT` can raise and jump to `fail`; comparator exceptions, their partial
permutation guarantee, and comparator-call events are outside this snapshot
model. Exact erasure is to the reviewed Lean `binarysort?` transcription within
that explicit delta, not to the omitted C exception path.

## Depends on

- [Array-access trace model](access-trace.md)
- [binarysort](../../transcription/binarysort.md)
- [sortslice primitive safety](sortslice-safe.md)

## Sources

- [Verbatim `binarysort`](../../../sources/listobject-excerpts.md#binarysort)
