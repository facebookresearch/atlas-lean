/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OffWalkExteriorEscape
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffWalkExteriorEscape`

* For the unit-square loop `sq` (support in `box 2 1`):
  * `oc_reachesExterior_of_row_ge_R`: the off-walk site `(3, 1)` escapes to the exterior.
  * The refutations: `oc_exists_support_not_leftRegion` (a vertex of `sq` is outside),
    `oc_not_hOutOff`, `oc_not_outsideReachesExterior`, `oc_not_outsideReachesTop`.
* `oc_ffc_reachable_eq_of_mem`: a removed site is isolated.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffWalkExteriorEscape

theorem adj_of {x y : Site 2} (h : ((x 0 - y 0).natAbs + (x 1 - y 1).natAbs) = 1) :
    (hypercubicLattice 2).Adj x y := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; exact h

/-- The counterclockwise boundary of the unit square `[0, 1]²`, a closed walk of length 4. -/
def sq : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] :=
  .cons (adj_of (x := ![0, 0]) (y := ![1, 0]) (by decide))
    (.cons (adj_of (x := ![1, 0]) (y := ![1, 1]) (by decide))
      (.cons (adj_of (x := ![1, 1]) (y := ![0, 1]) (by decide))
        (.cons (adj_of (x := ![0, 1]) (y := ![0, 0]) (by decide)) .nil)))

theorem sq_support_box : ∀ p ∈ sq.support, p ∈ box 2 1 := by
  intro p hp
  simp only [sq, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> (rw [mem_box]; intro i; fin_cases i <;> simp)

theorem sq_supportSet_box : oc_supportSet sq ⊆ box 2 1 := fun p hp => sq_support_box p hp

theorem off3 : (![3, 1] : Site 2) ∉ sq.support := by
  simp [sq]

example : ∃ e : Site 2, e ∈ exterior 2 1 ∧
    (ffc_offSupportLattice (oc_supportSet sq)).Reachable ![3, 1] e :=
  oc_reachesExterior_of_row_ge_R sq 1 sq_supportSet_box (by simp) off3

example : ∃ v ∈ sq.support, v ∉ jec_leftRegion sq ∧ ∀ p ∈ sq.support, v 0 ≤ p 0 :=
  oc_exists_support_not_leftRegion sq

example : ¬ ∀ s t : Site 2, s ∉ jec_leftRegion sq → t ∉ jec_leftRegion sq →
    ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ sq.support :=
  oc_not_hOutOff sq

example : ¬ oc_OutsideReachesExterior sq 1 := oc_not_outsideReachesExterior sq 1 sq_supportSet_box

example : ¬ oc_OutsideReachesTop sq 5 := oc_not_outsideReachesTop sq 5

example {y : Site 2} (h : (ffc_offSupportLattice {![0, 0]}).Reachable ![0, 0] y) : ![0, 0] = y :=
  oc_ffc_reachable_eq_of_mem (Set.mem_singleton _) h

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffWalkExteriorEscape
