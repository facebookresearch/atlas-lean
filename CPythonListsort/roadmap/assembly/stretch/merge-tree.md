---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listsort_mergeTree_cost_le_powerSort
---

# Implementation policy costs no more than the PowerSort tree

The public implementation bridge is
`listsort_mergeTree_cost_le_powerSort` in
`Code/Assembly/ListSortCostBound.lean:614`.  It has only the arbitrary
Boolean comparator, reverse flag, validated input, and platform size bound as
premises.  It returns the successful real execution's checked merge plan and
a `PowerMergePlanValid` canonical plan on the same exact formed-run profile,
with `implementationPlan.mergeCost ≤ powerSortPlan.mergeCost`.

For active inputs the stronger evidence is `ListSortActiveMergeCostPost` at
`Code/Assembly/ListSortCostBound.lean:41-86`.  It contains the exact
scan/collapse trace split, an execution-indexed proof that the displayed open
state is the state actually passed to `merge_force_collapse`, the historical
`ScanPowerForestInv`, the exact CPython collapse-cost relation, the literal
canonical-top-pair plan identity, and the final cost dominance.  The public
top-level construction that discharges initialization, reverse mode, scan
fuel, storage, and loop invariants is `listSortTraced_policyBridge_active` at
`Code/Assembly/ListSortPolicyBridge.lean:129`.

The final-collapse comparison is intentionally an inequality, not tree
equality.  `CPythonForceCollapseCost.le_topPairCompletionCost` is proved at
`Code/Assembly/MergeTreeCost.lean:273`; the strict third-last
rotation is isolated at `:213`.  The compiler-checked real 256-element
regression at `Code/Assembly/PowerSortCostRegression.lean:116`
pins formed lengths `[32,33,83,36,32,32,8]`, scan cost 213, CPython's
completion sequence `[40,68,108,256]` and total 685, and the canonical
sequence `[40,72,108,256]` and total 689.

Let `L` be the chronological positive run lengths actually pushed by a
successful real `list_sort_impl` execution and let `E` be its chronological
logical pre-trim merge events.  Replaying `E` from `L` must succeed and yield an
ordered full binary tree `T_impl` whose left-to-right leaves are exactly `L`.
The theorem derives all replay, adjacency, partition, and completion facts from
the execution; none is a caller premise.

For each boundary of this same formed-leaf partition, define `P_j` using the
transcribed finite-width `powerloop`.  Let `T_PS` be the Method-2-prime,
min-oriented Cartesian PowerSort tree for `P_1, ..., P_(r-1)`, with the tie
behavior fixed by Algorithm 2's strict `P.top() > p` test.  Prove the following
single implementation bridge:

1. the `found_new_run` events during the scan construct exactly the open forest
   obtained by the paper's left-to-right stack algorithm on `L` and `P`;
2. repeatedly merging the top pair of that open forest produces `T_PS`;
3. CPython's actual `merge_force_collapse` may produce a different alphabetic
   tree, but `mergeCost T_impl <= mergeCost T_PS`.

The third conclusion replaces the former, false final-tree-equality target.
When CPython chooses the third-last pair, its local change is
`A + (B + C)` to `(A + B) + C`.  The source guard `length A < length C`
makes the new local cost smaller by exactly `length C - length A`; a top-pair
choice agrees with the paper completion.  Compose these rotations through the
whole final collapse.

Adaptive minrun changes only the leaf partition to which the abstract policy
argument is applied.  Do not identify `L` with the first `2^mr_e` generator
outputs: a long natural run is consumed at its own length while advancing the
generator once, a forced run may cross an original natural-run boundary, and
the actual number of formed leaves need not be a power of two.

### Required executable regression

Use a 256-element input whose actual formed lengths are
`[32, 33, 83, 36, 32, 32, 8]`.  Here `mr_e = 3`, every generated target used is
32, the leaf starts are `[0, 32, 65, 148, 184, 216, 248]`, and the boundary
powers are `[3, 2, 1, 2, 3, 4]`.  The scan merges the first two leaves at cost
65 and their result with the third at cost 148, leaving lengths
`[148, 36, 32, 32, 8]` whose recomputed open-boundary powers are
`[1, 2, 3, 4]`.  The general reached-state certificate, rather than this
executable projection, is what ties those mathematical powers to the actual
pending records' stored fields.

Paper top-pair completion then costs `40 + 72 + 108 + 256 = 476`, for total
689.  CPython first pays 40, observes `36 < 40`, takes the third-last branch,
and pays `68 + 108 + 256`, for total 685.  The regression must expose both
merge sequences and totals; it prevents either tree equality or the
cost-dominance direction from being changed silently.  If it requires
`native_decide`, list it as a compiler-checked proof leaf in the trust ledger
before review.

## Depends on

- [Merge-cost accounting](merge-cost.md)
- [found_new_run](../../transcription/found-new-run.md)
- [`merge_force_collapse`](../../transcription/merge-force-collapse.md)
- [list_sort_impl](../../transcription/list-sort-impl.md)

## Proof depends on

- [Unconditional adaptive-minrun output band](../../bit-equivalence/minrun-output-range.md)
- [found_new_run preserves policy invariants](../../policy/found-new-run-preservation.md)
- [Boundary-power geometry for three consecutive runs](../../policy/boundary-power-geometry.md)
- [`merge_force_collapse` preserves pending-run layout](../../policy/force-collapse-preservation.md)

## Sources

- [Munro-Wild Cartesian-tree map](../../../sources/munro-wild-powersort-notes.md#monotonicity-and-cartesian-tree-interpretation)
- [Munro-Wild one-pass stack policy](../../../sources/munro-wild-powersort-notes.md#one-pass-stack-policy)
- [Verbatim `found_new_run`](../../../sources/listobject-excerpts.md#found-new-run)
- [Verbatim `merge_force_collapse`](../../../sources/listobject-excerpts.md#merge-force-collapse)
- [CPython adaptive-minrun explanation](../../../sources/listsort.md#computing-minrun)
