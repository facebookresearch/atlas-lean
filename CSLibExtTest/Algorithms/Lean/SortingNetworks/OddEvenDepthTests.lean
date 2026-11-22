/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.OddEvenDepth
public meta import CSLibExt.Algorithms.Lean.SortingNetworks.OddEvenDepth

/-!
# Odd-even merge sort depth tests

Executed fixtures (tabulated levels): the as-soon-as-possible depth of the odd-even sorter on
`2 ^ k` wires is `1, 3, 6, 10, 15` for `k = 1, …, 5`, exactly `k (k + 1) / 2`, and the merger's
on `2 ^ (k + 1)` wires is `k + 1`; the last layer has depth `1`. Each run throws on a mismatch.
Closed checks instantiate the theorems on the `Network` API.
-/

namespace Cslib.Algorithms.Lean.SortingNetworks.OddEven

open Bitonic

/-- The depth of a network on wires below `N`, as the highest tabulated level. -/
private meta def depthOf (ps : List (ℕ × ℕ)) (N : ℕ) : ℕ :=
  (levelsTab ps (List.replicate N 0)).foldl max 0

#eval do
  for k in [1, 2, 3, 4, 5] do
    let d := depthOf (oddEvenSortN k) (2 ^ k)
    unless 2 * d == k * (k + 1) do throw (IO.userError s!"k = {k}: sorter depth {d}")
  for k in [0, 1, 2, 3, 4] do
    let d := depthOf (oddEvenMerge k) (2 ^ (k + 1))
    unless d == k + 1 do throw (IO.userError s!"k = {k}: merger depth {d}")
    unless depthOf (finalLayer k) (2 ^ (k + 2)) == 1 do throw (IO.userError s!"last layer {k}")
  IO.println s!"odd-even sorter depths for k = 1..5: \
    {[1, 2, 3, 4, 5].map fun k => depthOf (oddEvenSortN k) (2 ^ k)}; merger depth k + 1"

/-! Closed checks -/

example : ∃ d, Network.DepthLE (oddEvenSorter 6) d ∧ 2 * d ≤ 6 * 7 := oddEvenSorter_depthLE 6

example (d : ℕ) (hd : Network.DepthLE (oddEvenSorter 6) d) : 6 ≤ d :=
  le_of_oddEvenSorter_depthLE hd

example : DepthLE (oddEvenMerge 5) 6 := depthLE_oddEvenMerge 5

#print axioms oddEvenSorter_depthLE
#print axioms depthLE_append_relabel

end Cslib.Algorithms.Lean.SortingNetworks.OddEven
