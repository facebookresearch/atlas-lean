/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.Kinship
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.Kinship` -/

open MathlibExt.Biology.StatisticalGenetics.Kinship

namespace MathlibExtTest.Kinship

/-! ### Pedigrees: full sibs and first cousins -/

/-- Founders `0, 1`; full sibs `2, 3`; their offspring `4` (also the non-vacuity witness for
`Pedigree`). -/
def fullSibs : Pedigree 5 where
  parents := ![none, none, some ![0, 1], some ![0, 1], some ![2, 3]]
  parents_lt := by
    intro i g h k
    fin_cases i <;> simp at h <;> subst h <;> fin_cases k <;> decide

/-- The offspring of full sibs has inbreeding coefficient `1/4`. -/
theorem fullSibs_kinshipInbreeding : fullSibs.kinshipInbreeding 4 = 1 / 4 := by
  have h0 : fullSibs.kinship 0 0 = 1 / 2 := fullSibs.kinship_self_of_parents_eq_none rfl
  have h01 : fullSibs.kinship 0 1 = 0 :=
    fullSibs.kinship_of_lt_of_parents_eq_none (by decide) rfl
  have h1 : fullSibs.kinship 1 1 = 1 / 2 := fullSibs.kinship_self_of_parents_eq_none rfl
  have h20 : fullSibs.kinship 2 0 = 1 / 4 := by
    rw [fullSibs.kinship_of_gt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
    norm_num [h0, fullSibs.kinship_comm 1 0, h01]
  have h21 : fullSibs.kinship 2 1 = 1 / 4 := by
    rw [fullSibs.kinship_of_gt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
    norm_num [h01, h1]
  have h23 : fullSibs.kinship 2 3 = 1 / 4 := by
    rw [fullSibs.kinship_of_lt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
    norm_num [h20, h21]
  simp only [Pedigree.kinshipInbreeding]
  exact h23

/-- Founders `0, 1, 4, 5`; full sibs `2, 3` (children of `0, 1`); `6` is a child of `2` and
`4`, `7` a child of `3` and `5`, so `6` and `7` are first cousins; `8` is their child. -/
def firstCousins : Pedigree 9 where
  parents := ![none, none, some ![0, 1], some ![0, 1], none, none, some ![2, 4],
    some ![3, 5], some ![6, 7]]
  parents_lt := by
    intro i g h k
    fin_cases i <;> simp at h <;> subst h <;> fin_cases k <;> decide

/-- The offspring of first cousins has inbreeding coefficient `1/16`. -/
example : firstCousins.kinshipInbreeding 8 = 1 / 16 := by
  set P := firstCousins
  have f : ∀ i j : Fin 9, i < j → P.parents j = none → P.kinship i j = 0 :=
    fun i j hij h => P.kinship_of_lt_of_parents_eq_none hij h
  have h00 : P.kinship 0 0 = 1 / 2 := P.kinship_self_of_parents_eq_none rfl
  have h11 : P.kinship 1 1 = 1 / 2 := P.kinship_self_of_parents_eq_none rfl
  have h01 : P.kinship 0 1 = 0 := f 0 1 (by decide) rfl
  have h20 : P.kinship 2 0 = 1 / 4 := by
    rw [P.kinship_of_gt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
    norm_num [h00, P.kinship_comm 1 0, h01]
  have h21 : P.kinship 2 1 = 1 / 4 := by
    rw [P.kinship_of_gt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
    norm_num [h01, h11]
  have h23 : P.kinship 2 3 = 1 / 4 := by
    rw [P.kinship_of_lt_of_parents_eq_some (g := ![0, 1]) (by decide) rfl]
    norm_num [h20, h21]
  have h25 : P.kinship 2 5 = 0 := f 2 5 (by decide) rfl
  have h34 : P.kinship 3 4 = 0 := f 3 4 (by decide) rfl
  have h45 : P.kinship 4 5 = 0 := f 4 5 (by decide) rfl
  have h63 : P.kinship 6 3 = 1 / 8 := by
    rw [P.kinship_of_gt_of_parents_eq_some (g := ![2, 4]) (by decide) rfl]
    norm_num [h23, P.kinship_comm 4 3, h34]
  have h65 : P.kinship 6 5 = 0 := by
    rw [P.kinship_of_gt_of_parents_eq_some (g := ![2, 4]) (by decide) rfl]
    norm_num [h25, h45]
  have h67 : P.kinship 6 7 = 1 / 16 := by
    rw [P.kinship_of_lt_of_parents_eq_some (g := ![3, 5]) (by decide) rfl]
    norm_num [h63, h65]
  simp only [Pedigree.kinshipInbreeding]
  exact h67

/-- Gene dropping on the full-sib pedigree gives the same inbreeding coefficient. -/
example : fullSibs.inbreeding 4 = 1 / 4 := by
  rw [Pedigree.inbreeding_eq_kinshipInbreeding, fullSibs_kinshipInbreeding]

/-! ### Wright's path formula -/

/-- The full-sib pedigree has no selfing, as required by Wright's path formula. -/
theorem fullSibs_noSelfing : fullSibs.NoSelfing := by
  intro i g h
  change ![none, none, some ![0, 1], some ![0, 1], some ![2, 3]] i = some g at h
  fin_cases i <;> simp at h
  all_goals subst g
  all_goals decide

private theorem fullSibs_ancPaths_zero :
    fullSibs.ancPaths 0 = {([0] : List (Fin 5))} := by
  ext q
  rw [Finset.mem_singleton, fullSibs.mem_ancPaths_of_parents_eq_none (i := 0) rfl]

private theorem fullSibs_ancPaths_one :
    fullSibs.ancPaths 1 = {([1] : List (Fin 5))} := by
  ext q
  rw [Finset.mem_singleton, fullSibs.mem_ancPaths_of_parents_eq_none (i := 1) rfl]

private theorem fullSibs_ancPaths_two :
    fullSibs.ancPaths 2 = {([2] : List (Fin 5)), [2, 0], [2, 1]} := by
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton,
    fullSibs.mem_ancPaths_of_parents_eq_some (i := 2) (g := ![0, 1]) rfl, Fin.exists_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, fullSibs_ancPaths_zero, fullSibs_ancPaths_one,
    exists_eq_left]

private theorem fullSibs_ancPaths_three :
    fullSibs.ancPaths 3 = {([3] : List (Fin 5)), [3, 0], [3, 1]} := by
  ext p
  simp only [Finset.mem_insert, Finset.mem_singleton,
    fullSibs.mem_ancPaths_of_parents_eq_some (i := 3) (g := ![0, 1]) rfl, Fin.exists_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, fullSibs_ancPaths_zero, fullSibs_ancPaths_one,
    exists_eq_left]

/-- The only ancestral path from sibling `2` to founder `0` has the expected direction. -/
example : fullSibs.pathsTo 2 0 = {([2, 0] : List (Fin 5))} := by
  ext p
  simp only [Pedigree.pathsTo, fullSibs_ancPaths_two, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hlast⟩
    rcases hp with rfl | rfl | rfl
    · norm_num at hlast
    · rfl
    · norm_num at hlast
  · rintro rfl
    norm_num

/-- Wright's path sum for the full siblings is `1/4`: founders `0` and `1` each contribute
`(1/2)^(2 + 2 - 1) = 1/8`. -/
example : fullSibs.kinship 2 3 = 1 / 4 := by
  rw [fullSibs.kinship_eq_sum_paths fullSibs_noSelfing]
  simp only [Pedigree.pathsTo, fullSibs_ancPaths_two, fullSibs_ancPaths_three]
  norm_num [Fin.sum_univ_succ, Finset.sum_filter, Finset.sum_insert, fullSibs,
    Pedigree.kinshipInbreeding, Pedigree.kinship]

/-- The inbreeding form of Wright's path formula gives the same `1/4` for the siblings'
offspring. -/
example : fullSibs.inbreeding 4 = 1 / 4 := by
  rw [fullSibs.inbreeding_eq_sum_paths fullSibs_noSelfing (g := ![2, 3]) rfl]
  simp_rw [Pedigree.inbreeding_eq_kinshipInbreeding]
  simp only [Pedigree.pathsTo, Matrix.cons_val_zero, Matrix.cons_val_one,
    fullSibs_ancPaths_two, fullSibs_ancPaths_three]
  norm_num [Fin.sum_univ_succ, Finset.sum_filter, Finset.sum_insert, fullSibs,
    Pedigree.kinshipInbreeding, Pedigree.kinship]

/-- A pedigree with selfing: `3` is a child of `1` and `1`. -/
def selfing : Pedigree 4 where
  parents := ![none, none, some ![0, 1], some ![1, 1]]
  parents_lt := by
    intro i g h k
    fin_cases i <;> simp at h <;> subst h <;> fin_cases k <;> decide

/-- With selfing the tabular recursion still applies: `F₃ = φ₁₁ = 1/2`; Wright's path formula
is stated only without selfing. -/
example : selfing.kinshipInbreeding 3 = 1 / 2 := by
  have h : selfing.kinship 1 1 = 1 / 2 := selfing.kinship_self_of_parents_eq_none rfl
  simp only [Pedigree.kinshipInbreeding]
  exact h

end MathlibExtTest.Kinship
