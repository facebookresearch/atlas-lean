/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ReachesExteriorConnected
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ReachesExteriorConnected`

* `arcxc_singlePoint_reachesExterior`: the criterion `arcxc_ReachesExterior` holds for `{(0, 0)}`
  with `R = 1` (a nonvacuous instance), hence by `arcxc_connected_of_reachesExterior` the
  complement of the origin is connected.
* `arcxc_leafRemovable_of_reachesExterior` applied to `S = ∅`.
* `arcxc_reachesExterior_of_rowClear`: from `(0, 3)`, with `B = {(0, 0)}`, the row is clear.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ReachesExteriorConnected

theorem origin_mem_box : (![0, 0] : Site 2) ∈ box 2 1 := by
  rw [mem_box]; intro i; fin_cases i <;> simp

example : arcxc_ReachesExterior ({![0, 0]} : Set (Site 2)) 1 :=
  arcxc_singlePoint_reachesExterior _ origin_mem_box

example : arcns_OffSupportConnected ({![0, 0]} : Set (Site 2)) :=
  arcxc_connected_of_reachesExterior (arcxc_singlePoint_reachesExterior _ origin_mem_box)

example : arcns_LeafRemovable (∅ : Set (Site 2)) ![0, 0] :=
  arcxc_leafRemovable_of_reachesExterior (R := 1) (by
    simpa using arcxc_singlePoint_reachesExterior _ origin_mem_box)

example : ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk ![0, 3] e),
    (∀ w ∈ p.support, w ∉ ({![0, 0]} : Set (Site 2))) ∧ e ∈ exterior 2 1 :=
  arcxc_reachesExterior_of_rowClear (fun t _ h => by
    have := congrFun (Set.mem_singleton_iff.1 h) 1
    simp at this)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ReachesExteriorConnected
