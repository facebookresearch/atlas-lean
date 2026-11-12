---
declaration: structure
origin: cited
statement: formalized
proof: formalized
lean: CPythonListsort.ListSortMergeCostPost
---

# Logical merge-cost and formed-run accounting

The formal accounting interface is `ListSortMergeCostPost` at
`Code/Assembly/ListSortCostBound.lean:95`.  On the genuine
`listSortTraced?` execution it exports the normalized replay, exact formed-run
profile, exact logical merge cost, weighted-path identity, and the adaptive
formed-length relation (`Code/Assembly/ListSortCostBound.lean:100-125`).
Its profile is a `RunProfile`, so positivity and exact sum-to-input are part of
the type rather than caller assumptions.

The raw observation types are `PendingPushEvent`, `LogicalMergeEvent`, and
`PolicyEvent` at `Code/Assembly/AccessTrace.lean:194-219`.
`pushFormedRunTraced` records the real post-extension push and has exact
erasure and legacy-trace projection theorems at
`Code/Assembly/AccessTrace.lean:1275-1339`.  A successful
`merge_at` exports exactly one event for the selected pre-trim adjacent runs in
the `MergeAtSafetyPost.logicalMerge` field at
`Code/Assembly/MergeAtSafety.lean:1672-1686`; `mergeAt_safe` proves
that postcondition at `Code/Assembly/MergeAtSafety.lean:2145`.  The kernel-checked
early-trim regression at `Code/Assembly/MergeAtSafety.lean:2213`
records that logical event while recording no directional memory event.

Empty and singleton executions are pinned against the actual evaluator by
`listSortTraced_policy_empty` and `listSortTraced_policy_singleton` at
`Code/Assembly/ListSortPolicyEndpoints.lean:58` and `:105`; both
raw traces are empty, while top-level normalization supplies the singleton
leaf `[1]` and both costs are zero.

Define one auditable accounting object for the real top-level evaluator.  Its
formed-run channel records, in scan order, the base, natural length returned by
`count_run`, adaptive target returned by `minrun_next`, and final length pushed
after the optional `binarysort`.  Its logical-merge channel records every
successful pending-stack combination with the two adjacent **pre-trim** run
lengths, base, and selected stack index.  The top-level theorem
`listSortTraced_policyBridge_active` at
`Code/Assembly/ListSortPolicyBridge.lean:129` proves the split at the
exact `merge_force_collapse` call boundary; the exported `traceSplit` and
`reachedCollapse` fields are visible at
`Code/Assembly/ListSortCostBound.lean:48-53`.  Thus each merge is
classified by its position as a scan (`found_new_run`) event or a
final-collapse event; the raw event does not carry an independently supplied
origin tag that could disagree with the composed evaluator.

The logical event must be emitted when `merge_at` combines the pending entries,
before its two trimming gallops.  It is distinct from the merge-memory event:
if trimming consumes all of one side, the C operation has still created an
internal merge-tree node of cost `left.length + right.length`, even though no
`merge_lo`/`merge_hi` call and hence no merge-memory event occurs.  Instrument
the actual composed evaluator and prove exact erasure; do not reconstruct a
purported trace after execution or count post-trim `na + nb`.

Define:

- a positive ordered leaf partition and the normalized leaf sequence used for
  the empty, singleton, and scanned cases (`[]`, `[1]`, and the actual formed
  events, respectively);
- replay validity for logical adjacent-run merges and the resulting ordered
  full binary tree;
- event cost `left.length + right.length`, trace cost as its sum, and tree cost
  as the sum of internal-node lengths;
- binary run-length entropy
  `H(L/N) = sum_i (L_i/N) * log2 (N/L_i)` for positive leaves summing to
  positive `N`, with the empty case stated separately rather than relying on
  Lean's totalized logarithm.

The main definition is complete only when the subsequent bridge can prove that
the real successful execution's formed leaves are positive, adjacent, and sum
to the input length; replay of all logical merge events succeeds; its tree has
those leaves in the same order; and trace cost equals tree cost.

The reverse-mode leaf sequence is the one discovered after CPython's initial
reverse.  No strict-weak-order premise is needed for these length and policy
observations: the comparator is an arbitrary total Boolean function.  Calling
the leaves “formed runs” does not assert that they are semantic sorted runs
under such a comparator.

### Required anti-vacuity checks

- A concrete already-ordered adjacent pair must produce one logical merge
  event of the two original lengths while producing no directional
  merge-memory event after trimming.
- Empty and singleton top-level inputs must have zero logical merge cost; the
  singleton accounting must still normalize to the one-leaf tree `[1]` even
  though `list_sort_impl` bypasses the scan loop.
- Exact erasure/noninterference theorems must show that adding both channels
  changes neither the evaluator result nor the already-reviewed access,
  push-depth, fuel, and merge-memory observations.

## Depends on

- [Array-access trace model](../safety/access-trace.md)
- [`merge_at`](../../transcription/merge-at.md)
- [`list_sort_impl`](../../transcription/list-sort-impl.md)

## Sources

- [Munro-Wild merge-cost definition](../../../sources/munro-wild-powersort-notes.md#merge-cost-and-entropy)
- [CPython adaptive-minrun explanation](../../../sources/listsort.md#computing-minrun)
- [Verbatim `merge_at`](../../../sources/listobject-excerpts.md#merge-at)
- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
