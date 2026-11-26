/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingColumnArc

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingColumnArc`

* `JcbColShift` holds for the all-closed configuration on a one-site box (so the hypothesis of
  `jcb_vsFix_arc_sides_of_vCrossing` is satisfiable), giving `CrossingArcSides` there.
* `jcb_upcross` on the one-step walk from `(0, 0)` to `(0, 1)`.
-/

@[expose] public section

open StatMech.Lattice StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CrossingColumnArc

/-- A site of the one-site box `[m, m] × [c, c]` is `(m, c)`. -/
theorem eq_of_mem_rect_point {m c : ℤ} {z : Site 2} (hz : z ∈ rect m m c c) :
    z = jsi_cell m c := by
  rw [mem_rect] at hz
  funext i
  fin_cases i
  · simp only [jsi_cell, Fin.zero_eta, Matrix.cons_val_zero]; omega
  · simp only [jsi_cell, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega

/-- `JcbColShift` for the all-closed configuration on `[m, m] × [c, c]`. -/
theorem colShift_point (m c : ℤ) (xB : Site 2) (hxB : xB ∈ rect m m c c) :
    JcbColShift (fun _ => false) m m c c xB hxB := by
  refine ⟨fun _ => m, fun _ _ _ => le_rfl, fun _ _ _ => le_rfl, fun r h1 h2 => ?_,
    fun r h1 h2 => by omega, rfl, fun _ => Or.inr (Or.inl (sub_self m))⟩
  rw [amo_overlapComp_allClosed, eq_of_mem_rect_point hxB, Set.mem_singleton_iff]
  have : r = c := le_antisymm h2 h1
  rw [this]

example (m c : ℤ) :
    StatMech.Universality.CrossingArcSides (fun _ => false) (m - 1) (m + 1) m m c c :=
  jcb_vsFix_arc_sides_of_vCrossing _ (by omega) (by omega) (colShift_point m c)

/-- `(0, 0)` and `(0, 1)` are adjacent in the square lattice. -/
theorem adj01 : (hypercubicLattice 2).Adj ![0, 0] ![0, 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; rfl

example : ∃ i, 1 ≤ i ∧ i ≤ (SimpleGraph.Walk.cons adj01 .nil).length ∧
    ((SimpleGraph.Walk.cons adj01 .nil).getVert i) 1 = 1 ∧
    ((SimpleGraph.Walk.cons adj01 .nil).getVert (i - 1)) 1 = 1 - 1 :=
  jcb_upcross (SimpleGraph.Walk.cons adj01 .nil) rfl rfl 1 zero_lt_one le_rfl

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CrossingColumnArc
