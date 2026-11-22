/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.Bubble
public import CSLibExt.Algorithms.Lean.SortingNetworks.Depth
public meta import CSLibExt.Algorithms.Lean.SortingNetworks.Bubble
public meta import CSLibExt.Algorithms.Lean.SortingNetworks.Depth

/-!
# Bubble network tests

Executed fixtures: for `n = 1, …, 8` the bubble network sorts all `2 ^ n` Boolean inputs
(`sortsBool`), has `n (n - 1) / 2` comparators, and its greedy depth (`levelsTab` of
`Network.toPairs`) is `2 n - 3` for `n ≥ 2`; dropping its last comparator breaks sorting for
`n ≥ 2`. Each run throws on a violation. Closed checks instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.SortingNetworks.Bubble

open Cslib.Algorithms.Lean.SortingNetworks

#eval do
  for n in [1, 2, 3, 4, 5, 6, 7, 8] do
    let net := bubble n
    unless sortsBool net do throw (IO.userError s!"n = {n}: does not sort")
    unless 2 * net.length == n * (n - 1) do throw (IO.userError s!"n = {n}: size")
    let depth := (Bitonic.levelsTab (Network.toPairs net) (List.replicate n 0)).foldl max 0
    if 2 ≤ n && depth != 2 * n - 3 then throw (IO.userError s!"n = {n}: depth {depth}")
    if 2 ≤ n && sortsBool net.dropLast then
      throw (IO.userError s!"n = {n}: sorts without its last comparator")
  IO.println "n = 1..8: bubble sorts, n(n-1)/2 comparators, depth 2n - 3, last comparator needed"

/-! Closed checks -/

example : Sorts (bubble 5) ℤ := bubble_sorts

example : 2 * (bubble 6).length = 30 := length_bubble

#print axioms bubble_sorts

end Cslib.Algorithms.Lean.SortingNetworks.Bubble
