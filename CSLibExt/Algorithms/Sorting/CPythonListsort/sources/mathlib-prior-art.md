# Mathlib prior-art map

The project pins Mathlib `v4.33.1` at commit
`0df444a360eaa60ab8c11dca51a86af692955474`. The following declarations were
checked in that source tree before refining the roadmap.

## Order assumptions

`Mathlib/Order/Defs/Unbundled.lean` defines
`IsStrictWeakOrder α r` for Prop-valued relations. The model should reuse that
class for the relation `fun a b => lt a b = true`, rather than introducing a
project class containing the desired sorting theorem.

## Sortedness and permutation

`Mathlib/Data/List/Sort.lean` uses `List.Pairwise` for sortedness and provides
the standard sorting and permutation API. `List.Perm` is suitable for the
top-level element-preservation conclusion. These are supporting APIs, not
existing proofs about CPython's implementation.

## Stability

Mathlib's list sorting code includes stable algorithms and examples, but the
pinned tree does not provide the occurrence-tagged, comparator-equivalence
stability predicate required by this project. Define that predicate locally on
indexed input occurrences and prove its relationship to the final output.

## Overlap search

A search of the pinned Lean and Mathlib trees and targeted public GitHub issue
and repository searches found no existing Lean formalization of CPython
listsort, TimSort, or PowerSort suitable for reuse. No roadmap node is marked
`mathlib: true` on the strength of these partial APIs.
