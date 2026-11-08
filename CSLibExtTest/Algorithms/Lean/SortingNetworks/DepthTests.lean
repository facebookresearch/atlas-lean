/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.Depth
public meta import CSLibExt.Algorithms.Lean.SortingNetworks.Depth

/-!
# Network depth tests

Executed fixtures (tabulated levels, checked against `levels` for `k ≤ 3`): the
as-soon-as-possible depth of the bitonic sorter on `2 ^ k` wires is `1, 3, 6, 10, 15` for
`k = 1, …, 5`, exactly `k (k + 1) / 2`, the bound of `depthLE_bitonicSortN`; the merger's depth
is `k`; reversing every comparator leaves the depth unchanged; a chain of comparators sharing a
wire has depth equal to its length; every output of the bitonic sorter (`k ≤ 3`) depends on all
`2 ^ k` inputs. Each run throws on a mismatch. Closed checks instantiate the theorems on the
`Network` API, including that no network of depth at most `1` sorts `4` wires.
-/

namespace Cslib.Algorithms.Lean.SortingNetworks.Bitonic

/-- The depth of a network on wires below `N`, as the highest tabulated level. -/
private meta def depthOf (ps : List (ℕ × ℕ)) (N : ℕ) : ℕ :=
  (levelsTab ps (List.replicate N 0)).foldl max 0

#eval do
  for k in [1, 2, 3, 4, 5] do
    let d := depthOf (bitonicSortN k 0) (2 ^ k)
    unless 2 * d == k * (k + 1) do throw (IO.userError s!"k = {k}: depth {d}")
    unless depthOf (bitonicMerge k 0) (2 ^ k) == k do throw (IO.userError s!"merge k = {k}")
    unless depthOf ((bitonicSortN k 0).map Prod.swap) (2 ^ k) == d do
      throw (IO.userError s!"swap changes depth at k = {k}")
  -- the table agrees with `levels` (small enough to evaluate directly)
  for k in [1, 2, 3] do
    let tab := levelsTab (bitonicSortN k 0) (List.replicate (2 ^ k) 0)
    unless (List.range (2 ^ k)).all fun x => tab.getD x 0 == levels (bitonicSortN k 0)
        (fun _ => 0) x do throw (IO.userError s!"table mismatch at k = {k}")
  let chain : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4)]
  unless depthOf chain 5 == 4 do throw (IO.userError "chain depth")
  IO.println s!"bitonic sorter depths for k = 1..5: \
    {[1, 2, 3, 4, 5].map fun k => depthOf (bitonicSortN k 0) (2 ^ k)}; merger depth k; \
    a 4-comparator chain has depth 4"

-- every output of the bitonic sorter depends on every input (so its smallest output has an
-- influence set of size `2 ^ k`, the bound behind `le_two_pow_of_sorts`)
#eval do
  for k in [1, 2, 3] do
    let S := influence (bitonicSortN k 0) fun x => {x}
    unless (List.range (2 ^ k)).all fun x => (S x).card == 2 ^ k do
      throw (IO.userError s!"influence at k = {k}")
  -- a network that compares only wires 0 and 1 leaves wire 0 independent of wire 2
  unless influence [(0, 1)] (fun x => {x}) 0 == {0, 1} do throw (IO.userError "influence")
  IO.println "bitonic sorter, k = 1..3: every output depends on all 2^k inputs"

/-! Closed checks -/

example (d : ℕ) (hd : DepthLE (bitonicSortN 6 0) d) : 6 ≤ d := le_of_depthLE_bitonicSortN hd

-- the same on the `Network` API
example : ∃ d, Network.DepthLE (bitonicSorter 6) d ∧ 2 * d ≤ 6 * 7 := bitonicSorter_depthLE 6

example (d : ℕ) (hd : Network.DepthLE (bitonicSorter 6) d) : 6 ≤ d :=
  le_of_bitonicSorter_depthLE hd

-- no network of depth at most `1` sorts `4` wires
example (net : Network 4) (h : Network.DepthLE net 1) : ¬ Sorts net Bool := fun hs => by
  have := Network.le_two_pow_of_sorts hs h
  omega

example (net : Network 5) : ofPairs 5 (Network.toPairs net) = net := Network.ofPairs_toPairs net


example : ∃ d, DepthLE (bitonicSortN 6 0) d ∧ 2 * d ≤ 6 * 7 := depthLE_bitonicSortN 6 0

example : DepthLE (bitonicMerge 6 0) 6 := depthLE_bitonicMerge 6 0

#print axioms depthLE_bitonicSortN
#print axioms depthLE_bitonicMerge
#print axioms DepthLE.append_disjoint
#print axioms getD_levelsTab
#print axioms le_two_pow_of_sorts
#print axioms Network.le_two_pow_of_sorts
#print axioms bitonicSorter_depthLE

end Cslib.Algorithms.Lean.SortingNetworks.Bitonic
