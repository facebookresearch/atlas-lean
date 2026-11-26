/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingVisitsRows

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingVisitsRows`

* For the all-closed configuration the overlap cluster of a site is that site.
* The refutation `amo_hasMonotoneArc_false` on `[0, 0] × [0, 1]`.
* `JsiHasMonotoneArc` does hold for the all-closed configuration on a one-site box `[m, m] × [c, c]`
  (so the predicate is satisfiable), and `jsi_arc_sides_of_hasMonotone` then gives
  `CrossingArcSides`.
-/

@[expose] public section

open StatMech.Lattice StatMech.RSW.Box
open StatMech.Universality (overlapComp)

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CrossingVisitsRows

/-- A site of the one-site box `[m, m] × [c, c]` is `(m, c)`. -/
theorem eq_of_mem_rect_point {m c : ℤ} {z : Site 2} (hz : z ∈ rect m m c c) :
    z = jsi_cell m c := by
  rw [mem_rect] at hz
  funext i
  fin_cases i
  · simp only [jsi_cell, Fin.zero_eta, Matrix.cons_val_zero]; omega
  · simp only [jsi_cell, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega

example : overlapComp (fun _ => false) 0 1 0 1 ![0, 0] (by simp [mem_rect]) = {![0, 0]} :=
  amo_overlapComp_allClosed 0 1 0 1 _ _

example : ¬ JsiHasMonotoneArc (fun _ => false) 0 0 0 1 :=
  amo_hasMonotoneArc_false le_rfl zero_lt_one

/-- On a one-site box the all-closed configuration has a monotone arc in every overlap cluster. -/
theorem hasMonotoneArc_point (m c : ℤ) : JsiHasMonotoneArc (fun _ => false) m m c c := by
  intro xB hxB
  rw [amo_overlapComp_allClosed, eq_of_mem_rect_point hxB]
  have hpt : ∀ z : Site 2, c ≤ z 1 → z 1 ≤ c → m ≤ z 0 → z 0 ≤ m → z ∈ ({jsi_cell m c} :
      Set (Site 2)) := fun z h1 h2 h3 h4 =>
    eq_of_mem_rect_point (by rw [mem_rect]; omega)
  exact ⟨{ col := fun _ => m
           band_lo := fun _ _ _ => le_rfl
           band_hi := fun _ _ _ => le_rfl
           shift := fun _ h1 h2 => by omega
           on_arc := fun z h1 h2 _ h3 h4 => hpt z h1 h2 h3 h4
           cd := le_rfl
           shift_all := fun _ => Or.inr (Or.inl (sub_self m))
           corner := fun z h1 h2 _ h3 h4 => hpt z h1 h2 h3 h4 }⟩

example (m c : ℤ) :
    StatMech.Universality.CrossingArcSides (fun _ => false) (m - 1) (m + 1) m m c c :=
  jsi_arc_sides_of_hasMonotone _ (by omega) (by omega) (hasMonotoneArc_point m c)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CrossingVisitsRows
