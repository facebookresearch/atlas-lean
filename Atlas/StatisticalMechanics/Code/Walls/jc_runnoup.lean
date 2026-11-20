/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Lattice.EarExistence
import Code.Lattice.EarRemoval

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice














structure jc_IsTopRowRun (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop where
  
  isExtreme : IsExtremeCell K c
  
  len_nonneg : 0 ≤ len
  
  run_mem : ∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, 0]) ∈ K
  
  right_stop : (c + ![len + 1, 0]) ∉ K













theorem jc_run_no_up (K : Set (Site 2)) (c : Site 2) (len : ℤ) (hrun : jc_IsTopRowRun K c len)
    (j : ℤ) : (c + ![j, 1]) ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hrun.isExtreme
  rw [Pi.add_apply]; simp





theorem jc_left_end_left_nmem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) : (c + ![(-1 : ℤ), 0]) ∉ K := by
  apply extremeCell_not_mem_of_left K c _ hrun.isExtreme
  · rw [Pi.add_apply]; simp
  · rw [Pi.add_apply]; simp




theorem jc_right_end_right_nmem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) : (c + ![len + 1, 0]) ∉ K :=
  hrun.right_stop




theorem jc_run_mem (K : Set (Site 2)) (c : Site 2) (len : ℤ) (hrun : jc_IsTopRowRun K c len)
    (j : ℤ) (hj0 : 0 ≤ j) (hj1 : j ≤ len) : (c + ![j, 0]) ∈ K :=
  hrun.run_mem j hj0 hj1








theorem jc_runFrame (K : Set (Site 2)) (c : Site 2) (len : ℤ) (hrun : jc_IsTopRowRun K c len) :
    (∀ j : ℤ, (c + ![j, 1]) ∉ K) ∧ (c + ![(-1 : ℤ), 0]) ∉ K ∧ (c + ![len + 1, 0]) ∉ K :=
  ⟨fun j => jc_run_no_up K c len hrun j,
   jc_left_end_left_nmem K c len hrun,
   jc_right_end_right_nmem K c len hrun⟩








theorem jc_domino_isExtremeCell : IsExtremeCell domino (![0, 0] : Site 2) where
  mem := origin_mem_domino
  maximal := by
    intro v hv
    rw [mem_domino_coord_iff] at hv
    unfold lexKey
    rw [Prod.Lex.toLex_le_toLex]
    rcases hv with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> (right; simp [h0, h1])




theorem jc_domino_isTopRowRun : jc_IsTopRowRun domino (![0, 0] : Site 2) 1 where
  isExtreme := jc_domino_isExtremeCell
  len_nonneg := by norm_num
  run_mem := by
    intro j hj0 hj1
    rw [mem_domino_coord_iff]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · left; refine ⟨?_, ?_⟩ <;> (rw [Pi.add_apply]; simp)
    · right; refine ⟨?_, ?_⟩ <;> (rw [Pi.add_apply]; simp)
  right_stop := by
    apply not_mem_domino
    refine fun h => ?_
    rcases h with ⟨h0, _⟩ | ⟨h0, _⟩ <;> (rw [Pi.add_apply] at h0; simp at h0)




theorem jc_domino_runFrame :
    (∀ j : ℤ, ((![0, 0] : Site 2) + ![j, 1]) ∉ domino) ∧
      ((![0, 0] : Site 2) + ![(-1 : ℤ), 0]) ∉ domino ∧
      ((![0, 0] : Site 2) + ![(1 : ℤ) + 1, 0]) ∉ domino :=
  jc_runFrame domino (![0, 0]) 1 jc_domino_isTopRowRun


theorem jc_unitCell_isExtremeCell : IsExtremeCell unitCell (![0, 0] : Site 2) where
  mem := origin_mem_unitCell
  maximal := by
    intro v hv
    simp only [unitCell, Set.mem_singleton_iff] at hv
    subst hv
    exact le_refl _




theorem jc_unitCell_isTopRowRun : jc_IsTopRowRun unitCell (![0, 0] : Site 2) 0 where
  isExtreme := jc_unitCell_isExtremeCell
  len_nonneg := le_refl _
  run_mem := by
    intro j hj0 hj1
    have hj : j = 0 := by omega
    subst hj
    simp only [unitCell, Set.mem_singleton_iff]
    funext i; fin_cases i <;> (rw [Pi.add_apply]; simp)
  right_stop := by
    apply not_mem_unitCell
    left
    rw [Pi.add_apply]; simp




theorem jc_unitCell_runFrame :
    (∀ j : ℤ, ((![0, 0] : Site 2) + ![j, 1]) ∉ unitCell) ∧
      ((![0, 0] : Site 2) + ![(-1 : ℤ), 0]) ∉ unitCell ∧
      ((![0, 0] : Site 2) + ![(0 : ℤ) + 1, 0]) ∉ unitCell :=
  jc_runFrame unitCell (![0, 0]) 0 jc_unitCell_isTopRowRun

end Walls

end StatMech
