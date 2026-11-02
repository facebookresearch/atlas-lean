/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportExteriorCovered
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportExteriorCovered`

* `orc_reachesExterior_of_anyClear` for the unit-square loop `sq` and the site `(0, 2)` above it
  (its upward column is clear).
* The refutation `orc_not_exteriorCovered` for `sq`.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffSupportExteriorCovered

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

example : ∃ e : Site 2, e ∈ exterior 2 1 ∧
    (ffc_offSupportLattice (oc_supportSet sq)).Reachable ![0, 2] e :=
  orc_reachesExterior_of_anyClear sq 1 (Or.inl (fun w hw => by
    obtain ⟨t, ht, rfl⟩ := (sw_vertSeg_mem_support _ _ _ _).1 hw
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_one] at ht
    rw [Set.mem_uIcc] at ht
    have : t = 2 := by omega
    subst this
    simp [sq]))

example (b : Site 2) : ¬ orc_ExteriorCovered sq b := orc_not_exteriorCovered sq b

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffSupportExteriorCovered
