/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BeaconFloodFill
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.BeaconFloodFill`

* For the unit-square loop `sq` with `R = 1`: the exterior lies in the beacon flood fill
  (`ocov_exterior_subset_beaconFill`), so does the off-walk site `(3, 1)`
  (`ocov_row_ge_R_in_beaconFill`); the flood fill lies outside `sq`
  (`ocov_beaconFill_subset_outside`); and the refutation `ocov_not_beaconCovers`.
* `ocov_beacon_mem_exterior`.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.BeaconFloodFill

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

example : beacon 2 1 ∈ exterior 2 1 := ocov_beacon_mem_exterior 1

example : exterior 2 1 ⊆ ffc_floodFill (oc_supportSet sq) (beacon 2 1) :=
  ocov_exterior_subset_beaconFill sq 1 sq_supportSet_box

example : (![3, 1] : Site 2) ∈ ffc_floodFill (oc_supportSet sq) (beacon 2 1) :=
  ocov_row_ge_R_in_beaconFill sq 1 sq_supportSet_box (by simp) (by simp [sq])

example : ffc_floodFill (oc_supportSet sq) (beacon 2 1) ⊆ (jec_leftRegion sq)ᶜ :=
  ocov_beaconFill_subset_outside sq 1 sq_support_box

example : ¬ (jec_leftRegion sq)ᶜ ⊆ ffc_floodFill (oc_supportSet sq) (beacon 2 1) :=
  ocov_not_beaconCovers sq 1 sq_supportSet_box

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.BeaconFloodFill
