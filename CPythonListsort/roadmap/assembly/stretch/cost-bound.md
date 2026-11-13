---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listsort_mergeCost_bound
---

# Nearly-optimal merge-cost bound

The headline theorem is `listsort_mergeCost_bound` at
`Code/Assembly/ListSortCostBound.lean:596`.  Its complete public
premise list is an arbitrary total Boolean comparator, `reverse`, a validated
`ListSortInput`, and `input.slice.entries.size ≤ PY_LIST_MAX`; no order law,
fuel, storage, liveness, run-partition, trace, or tree premise is exposed.  It
returns an actual successful result together with `ListSortMergeCostPost`.

The postcondition states the exact trace cost and profile and then exports
both quantitative conclusions at
`Code/Assembly/ListSortCostBound.lean:126-135`:

```text
(M_impl : Real) ≤ N * profile.entropy + 2 * N
(M_impl : Real) ≤ optimalAlphabeticMergeCost profile.lengths + 2 * N.
```

`PowerMergePlanValid.mergeCost_le_entropy_add_two_of_profile` supplies the
paper bound at `Code/Assembly/PowerTreeEntropy.lean:289`; the
alphabetic entropy lower bound and optimum corollary are
`RunProfile.entropy_mul_le_optimalAlphabeticMergeCost` and
`mergeCost_le_optimalAlphabetic_add_two` at
`Code/Assembly/AlphabeticCostBound.lean:336` and `:362`.
The exact empty and singleton conclusions are fields of the same public
postcondition at `Code/Assembly/ListSortCostBound.lean:136-157`, so
the zero case does not rely on totalized logarithm or division.

For an arbitrary total Boolean comparator, either value mode, either reverse
mode, a validated top-level input, and only the existing
`input.length <= PY_LIST_MAX` premise, obtain the real successful
`list_sort_impl` result and its logical policy accounting.  No caller-supplied
run partition, tree, trace validity, minrun-cycle premise, strict weak order,
or fuel premise may remain in the public theorem.

Let `N` be the input length, `L_1, ..., L_r` the implementation-formed leaf
lengths from that accounting, and `M_impl` the sum of the logical pre-trim
merge-event costs.  Export the exact conclusions that the leaves are positive
and sum to `N`, the event replay is the implementation's alphabetic merge tree,
and, for positive `N`,

```text
(M_impl : Real)
  <= N * H(L_1 / N, ..., L_r / N) + 2 * N.
```

State the empty and singleton executions explicitly with merge cost zero; do
not make the result depend on Lean's totalized division or logarithm at zero.
The proof first bounds the implementation by the Method-2-prime PowerSort tree
using the implementation bridge, then applies Theorem 1(iii)/Theorem 6 to the
positive probabilities `L_i/N`, whose sum-one premise comes from the actual
formed-run partition.

This is a bound relative to CPython's **formed** leaves after adaptive
extension.  It is not a bound relative to the original maximal-natural-run
vector and not a claim that those leaves equal the balanced minrun target
cycle.  It also does not transfer Theorem 6's comparison-count conclusion:
CPython adds binary insertion extension and uses different run discovery,
galloping, and directional merges.  The concrete `listsort_safe` theorem at
`Code/Assembly/ListSortSafety.lean:14-27` already proves the recorded
stack-depth bound and owns implementation stack capacity; this node need not
restate the paper's asymptotic space result.

As a useful corollary, define the optimal alphabetic merge cost on the same
formed leaf vector and conclude `M_impl <= OPT(L) + 2 * N` from the entropy
lower bound.  Keep this subordinate to the entropy inequality above, which is
the unique main result corresponding to the cited theorem.

## Depends on

- [Merge-cost accounting](merge-cost.md)

## Proof depends on

- [Implementation policy costs no more than the PowerSort tree](merge-tree.md)

## Sources

- [Munro-Wild optional cost theorem map](../../../sources/munro-wild-powersort-notes.md#optional-cost-theorem)
- [Munro-Wild nearly-optimal search-tree bound](../../../sources/munro-wild-powersort-notes.md#nearly-optimal-search-tree-bound)
- [CPython adaptive-minrun explanation](../../../sources/listsort.md#computing-minrun)
