/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.CrossingParity
import Code.Lattice.WindingWitness
import Code.Walls.wndwinding
import Code.Walls.wnuupperhalf
import Code.Walls.wnaalternate
import Code.Walls.wcbcolumnbridge
import Code.Walls.wstsigntoggle
import Code.Walls.rpccrossflip
import Code.Walls.wisindicatorsteps
import Code.Walls.wosorientedsign
import Code.Walls.welenterleave

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice

open StatMech.Walls







theorem wob_rayEdge_eq_hCrossEdge (z : Site 2) (c : ℤ) :
    wcb_canonRayEdge z c = rpc_hCrossEdge (![c, z 1] : Site 2) := by
  unfold wcb_canonRayEdge rpc_hCrossEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]



theorem wob_signStep_ne_zero_col (z u v : Site 2) (h : wnd_signStep z u v ≠ 0) :
    jec_rayEdge z s(u, v) :=
  (wnd_signStep_ne_zero_iff z u v).mp h






noncomputable def wob_indJump (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c : ℤ) : ℤ :=
  wis_ind z Vc (c + 1) - wis_ind z Vc c


theorem wob_indJump_mem (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (c : ℤ) :
    wob_indJump z Vc c = 1 ∨ wob_indJump z Vc c = 0 ∨ wob_indJump z Vc c = -1 := by
  unfold wob_indJump
  rcases wis_ind_in_01 z Vc (c + 1) with h1 | h1 <;>
    rcases wis_ind_in_01 z Vc c with h0 | h0 <;> rw [h1, h0] <;> simp




theorem wob_indJump_ne_zero_iff (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c : ℤ) :
    wob_indJump z Vc c ≠ 0 ↔ Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) := by
  unfold wob_indJump
  rw [sub_ne_zero, wis_ind_step_neq_iff z Vc c]




theorem wob_indJump_parity (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (c : ℤ) :
    wob_indJump z Vc c % 2 =
      (if Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) then (1 : ℤ) else 0) % 2 := by
  by_cases hodd : Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2)))
  · rw [if_pos hodd]
    have hne : wob_indJump z Vc c ≠ 0 := (wob_indJump_ne_zero_iff z Vc c).mpr hodd
    rcases wob_indJump_mem z Vc c with h | h | h
    · rw [h]
    · exact absurd h hne
    · rw [h]; decide
  · rw [if_neg hodd]
    have h0 : wob_indJump z Vc c = 0 := by
      by_contra hc; exact hodd ((wob_indJump_ne_zero_iff z Vc c).mp hc)
    rw [h0]


















def wob_ColumnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ (c₀ : ℤ) (N : ℕ), wis_indSeq z Vc c₀ 0 = 0 ∧
    (wcb_columnSorted z Vc = wis_nonzeroDiffs (wis_indSeq z Vc c₀) N ∨
     wcb_columnSorted z Vc =
       (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N).map (fun x => -x))





theorem wob_columnSortedEqJumps_iff_orientationConsistent (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    wob_ColumnSortedEqJumps z Vc ↔ wel_OrientationConsistent z Vc := Iff.rfl








theorem wob_orientationConsistent_of_columnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_ColumnSortedEqJumps z Vc) :
    wel_OrientationConsistent z Vc :=
  (wob_columnSortedEqJumps_iff_orientationConsistent z Vc).mp h




theorem wob_signsAlternate_of_columnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_ColumnSortedEqJumps z Vc) :
    wos_SignsAlternateInColumnOrder z Vc :=
  wel_signsAlternate_of_orientationConsistent z Vc
    (wob_orientationConsistent_of_columnSortedEqJumps z Vc h)



theorem wob_columnAlternates_of_columnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_ColumnSortedEqJumps z Vc) :
    wna_ColumnAlternates z Vc :=
  wel_columnAlternates_of_orientationConsistent z Vc
    (wob_orientationConsistent_of_columnSortedEqJumps z Vc h)




theorem wob_signedCross_pm_one_of_columnSortedEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_ColumnSortedEqJumps z Vc)
    (hodd : ¬ Even (jec_rayCount z Vc)) :
    wnd_signedCross z Vc = 1 ∨ wnd_signedCross z Vc = -1 :=
  wel_signedCross_pm_one z Vc (wob_orientationConsistent_of_columnSortedEqJumps z Vc h) hodd
















def wob_SignStepMatchesJump (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  wob_ColumnSortedEqJumps z Vc



theorem wob_orientationConsistent_of_signStepMatchesJump (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wob_SignStepMatchesJump z Vc) :
    wel_OrientationConsistent z Vc :=
  wob_orientationConsistent_of_columnSortedEqJumps z Vc h






theorem wob_canonicalUpDart_signStep (z : Site 2) (c : ℤ) (hc : c ≤ z 0 - 1) :
    wnd_signStep z (![c, z 1 - 1] : Site 2) (![c, z 1] : Site 2) = 1 := by
  unfold wnd_signStep
  rw [if_pos]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [hc]



theorem wob_canonicalUpDart_signStep_zero (z : Site 2) (c : ℤ) (hc : z 0 - 1 < c) :
    wnd_signStep z (![c, z 1 - 1] : Site 2) (![c, z 1] : Site 2) = 0 := by
  unfold wnd_signStep
  rw [if_neg, if_neg] <;>
    · rintro ⟨⟨_, hle⟩, _⟩; simp only [Matrix.cons_val_zero] at hle; omega









theorem wob_unitSquare_indSeq0 :
    wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 0 = 0 := by
  show wis_ind (![1, 1] : Site 2) wwit_unitSquareLoop (0 + ((0 : ℕ) : ℤ)) = 0
  unfold wis_ind
  rw [show ((![1, 1] : Site 2) 1) = 1 from by simp,
    show ((0 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from by simp, wis_unitSquare_rayCount0]
  decide


theorem wob_unitSquare_indSeq1 :
    wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 1 = 1 := by
  show wis_ind (![1, 1] : Site 2) wwit_unitSquareLoop (0 + ((1 : ℕ) : ℤ)) = 1
  unfold wis_ind
  rw [show ((![1, 1] : Site 2) 1) = 1 from by simp,
    show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = 1 from by simp, wis_unitSquare_rayCount1]
  decide





theorem wob_unitSquare_columnSortedEqJumps :
    wob_ColumnSortedEqJumps (![1, 1] : Site 2) wwit_unitSquareLoop := by
  refine ⟨0, 1, wob_unitSquare_indSeq0, Or.inl ?_⟩
  rw [wcb_unitSquare_columnSorted]
  
  unfold wis_nonzeroDiffs
  rw [show (List.range 1) = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [wob_unitSquare_indSeq1, wob_unitSquare_indSeq0]
  norm_num


theorem wob_Ltromino_indSeq0 :
    wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 0 = 0 := by
  show wis_ind (![1, 1] : Site 2) wnu_LtrominoLoop (0 + ((0 : ℕ) : ℤ)) = 0
  unfold wis_ind
  rw [show ((![1, 1] : Site 2) 1) = 1 from by simp,
    show ((0 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from by simp, wis_Ltromino_rayCount0]
  decide


theorem wob_Ltromino_indSeq1 :
    wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 1 = 1 := by
  show wis_ind (![1, 1] : Site 2) wnu_LtrominoLoop (0 + ((1 : ℕ) : ℤ)) = 1
  unfold wis_ind
  rw [show ((![1, 1] : Site 2) 1) = 1 from by simp,
    show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = 1 from by simp, wis_Ltromino_rayCount1]
  decide






theorem wob_Ltromino_columnSortedEqJumps :
    wob_ColumnSortedEqJumps (![1, 1] : Site 2) wnu_LtrominoLoop := by
  refine ⟨0, 1, wob_Ltromino_indSeq0, Or.inr ?_⟩
  rw [wcb_Ltromino_columnSorted]
  unfold wis_nonzeroDiffs
  rw [show (List.range 1) = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [wob_Ltromino_indSeq1, wob_Ltromino_indSeq0]
  norm_num













theorem wob_doubleSquare_not_columnSortedEqJumps :
    ¬ wob_ColumnSortedEqJumps (![1, 1] : Site 2) wnu_doubleSquare := by
  intro h
  exact wel_doubleSquare_not_orientationConsistent
    (wob_orientationConsistent_of_columnSortedEqJumps _ _ h)

























































end Lattice

end StatMech
