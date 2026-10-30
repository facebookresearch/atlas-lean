/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportConnected
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportConnected`

* `arcns_singlePoint_connected` and the bridge `arcns_offSupportConnected_iff_preconnected`: the
  lattice minus the origin is connected, also as preconnectedness of the induced graph.
* `arcns_farLeft_connected` for `B = {(0, 0)}`: `(-1, 5)` and `(-3, -2)` are joined avoiding `B`.
* `arcns_leafRemovable_empty`: inserting one site into the empty set keeps the complement
  connected. (`arcns_LeafRemovable` is false in general, see `lrc_leafRemovable_false`.)
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffSupportConnected

example : arcns_OffSupportConnected ({![0, 0]} : Set (Site 2)) := arcns_singlePoint_connected _

example : ((hypercubicLattice 2).induce ({![0, 0]} : Set (Site 2))ᶜ).Preconnected :=
  (arcns_offSupportConnected_iff_preconnected _).1 (arcns_singlePoint_connected _)

example : ∃ p : (hypercubicLattice 2).Walk ![-1, 5] ![-3, -2],
    ∀ w ∈ p.support, w ∉ ({![0, 0]} : Set (Site 2)) :=
  arcns_farLeft_connected _ 0 (fun q hq => by simp_all) _ _ (by simp) (by simp)

example : arcns_LeafRemovable (∅ : Set (Site 2)) ![4, 4] := arcns_leafRemovable_empty _

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffSupportConnected
