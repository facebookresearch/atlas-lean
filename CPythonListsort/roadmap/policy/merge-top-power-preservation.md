---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeTop_preserves_poweredPrefix
---

# Top merge preserves the powered prefix

Quantify `state`, `scanned`, a list `before`, top runs `left` and `right`, a
prospective `newRun`, powers `pInternal q : Nat`, and a `MergeAtResult result`.
Assume all of the following:

- `state.listlen.toNat ≤ PY_LIST_MAX`, `PendingLayout state scanned`, and
  `PoweredPrefix state`;
- the exact top-pair decomposition
  `state.pending.toList = before ++ [left, right]`;
- `newRun.base = state.basekeys + scanned`, `newRun.len.Nonnegative`,
  `0 < newRun.len.toNat`,
  `scanned + newRun.len.toNat ≤ state.listlen.toNat`, and
  `newRun ∉ state.pending.toList`; its stored `power` field is arbitrary;
- `left.power = some pInternal`,
  `pInternal = pendingBoundaryPower state.basekeys state.listlen left right`,
  and the exact fixed ghost candidate
  `q = pendingBoundaryPower state.basekeys state.listlen right newRun`;
- the strict loop guard `q < pInternal`; and
- `mergeAt? state (state.pending.size - 2) = some result`, with
  `result.returnCode = 0` and `result.fuelExhausted = false`.

With `merged := { left with len := left.len + right.len }`, prove the exact
post-merge decomposition `result.state.pending.toList = before ++ [merged]`,
`merged.power = some pInternal`, `PendingLayout result.state scanned`, and
`PoweredPrefix result.state`. Also prove
`q = pendingBoundaryPower result.state.basekeys result.state.listlen merged newRun`.
This is the recursive loop-preservation lemma: the candidate is not recomputed
after a merge.

The physical `merged.power` remains `some pInternal`, because `mergeAt?`
changes the length and carries the left run's field through the splice. It is
therefore stale—indeed `q < pInternal`—and the conclusion must not claim that it
stores `q` or exactly labels the prospective boundary. `PoweredPrefix` leaves
the newest pending run's field unconstrained. Exactness on the virtual list
`result.state.pending.toList ++ [newRun]` is required only at the eventual
`ReadyToPush` stop, after `setTopPower` overwrites this field with `q`.

For older stored boundaries, strict increase gives a lower power than
`pInternal`; right absorption preserves such a label when `right` is absorbed
into `left`. Left absorption under `q < pInternal` preserves the ghost
candidate when `left` is absorbed into `right`'s left side. These are geometry
obligations, not consequences of array splicing. The list-length premise is
the selected top-level input/allocation bound and is preserved because
`mergeAt?` does not change `listlen`.

## Depends on

- [Pending-run layout invariant](pending-layout.md)
- [Powered-prefix invariant](stack-powers.md)
- [merge_at](../transcription/merge-at.md)

## Proof depends on

- [merge_at preserves pending layout](merge-at-preservation.md)
- [powerloop terminating-result characterization](../bit-equivalence/powerloop-result.md)
- [Boundary-power geometry for three consecutive runs](boundary-power-geometry.md)

## Sources

- [Verbatim `merge_at`](../../sources/listobject-excerpts.md#merge-at)
- [Verbatim `found_new_run`](../../sources/listobject-excerpts.md#found-new-run)
- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [Verbatim `list_sort_impl`](../../sources/listobject-excerpts.md#list-sort-impl)
- [Verbatim list-allocation guard](../../sources/listobject-excerpts.md#list-resize)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
