/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectFaithfulJordanCrossing



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

private theorem exists_natAbs_bound_of_mem_list
    (l : List (Site 2)) :
    ∃ M : Nat, ∀ z ∈ l, (z 1).natAbs <= M := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨max (a 1).natAbs M, ?_⟩
      intro z hz
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Nat.le_max_left _ _
      · exact (hM z hz).trans (Nat.le_max_right _ _)



theorem exists_fkRectFaithfulWalk_vertical_natAbs_bound
    {x y : Site 2} (W : (hypercubicLattice 2).Walk x y) :
    ∃ M : Nat, ∀ z ∈ W.support,
      -(M : Int) <= z 1 ∧ z 1 <= (M : Int) := by
  obtain ⟨M, hM⟩ := exists_natAbs_bound_of_mem_list W.support
  refine ⟨M, ?_⟩
  intro z hz
  have habs := hM z hz
  have habsInt : ((z 1).natAbs : Int) <= (M : Int) := by
    exact_mod_cast habs
  rw [Int.natCast_natAbs] at habsInt
  exact ⟨(neg_le_of_abs_le habsInt), (le_of_abs_le habsInt)⟩

end StatMech.FrontierD
