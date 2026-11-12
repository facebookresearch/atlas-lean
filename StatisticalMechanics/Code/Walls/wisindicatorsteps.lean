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
import Code.Walls.umffullrev
import Code.Walls.wndwinding
import Code.Walls.wnuupperhalf
import Code.Walls.wnaalternate
import Code.Walls.wcbcolumnbridge
import Code.Walls.wstsigntoggle
import Code.Walls.rpccrossflip

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice

open StatMech.Walls







noncomputable def wis_ind (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c : ℤ) : ℤ :=
  (jec_rayCount (![c, z 1] : Site 2) Vc : ℤ) % 2


theorem wis_ind_in_01 (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (c : ℤ) :
    wis_ind z Vc c = 0 ∨ wis_ind z Vc c = 1 := by
  unfold wis_ind
  have h := Int.emod_two_eq_zero_or_one (jec_rayCount (![c, z 1] : Site 2) Vc : ℤ)
  tauto



theorem wis_rowCell_step (z : Site 2) (c : ℤ) :
    (![c + 1, z 1] : Site 2) 0 = (![c, z 1] : Site 2) 0 + 1 ∧
      (![c + 1, z 1] : Site 2) 1 = (![c, z 1] : Site 2) 1 := by
  constructor <;> simp












theorem wis_ind_step_neq_iff (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c : ℤ) :
    wis_ind z Vc (c + 1) ≠ wis_ind z Vc c ↔
      Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) := by
  have hstep := wis_rowCell_step z c
  have hflip := rpc_horizontalFlip_iff Vc (![c, z 1] : Site 2) (![c + 1, z 1] : Site 2)
    hstep.1 hstep.2
  
  rw [← hflip]
  unfold wis_ind
  set pc := jec_rayCount (![c, z 1] : Site 2) Vc with hpc
  set pc1 := jec_rayCount (![c + 1, z 1] : Site 2) Vc with hpc1
  
  have hpar : ∀ n : ℕ, (Even n ↔ (n : ℤ) % 2 = 0) := by
    intro n
    rw [← Int.even_coe_nat, Int.even_iff]
  constructor
  · intro hne
    have h0 := hpar pc
    have h1 := hpar pc1
    have hpc01 := Int.emod_two_eq_zero_or_one (pc : ℤ)
    have hpc101 := Int.emod_two_eq_zero_or_one (pc1 : ℤ)
    by_cases hep : Even pc <;> by_cases hep1 : Even pc1 <;>
      first | (simp_all; done) | (simp_all; omega)
  · intro hiff
    have h0 := hpar pc
    have h1 := hpar pc1
    have hpc01 := Int.emod_two_eq_zero_or_one (pc : ℤ)
    have hpc101 := Int.emod_two_eq_zero_or_one (pc1 : ℤ)
    by_cases hep : Even pc <;> by_cases hep1 : Even pc1 <;>
      first | (simp_all; done) | (simp_all; omega)


















def wis_nonzeroDiffs (f : ℕ → ℤ) (n : ℕ) : List ℤ :=
  ((List.range n).map (fun i => f (i + 1) - f i)).filter (fun d => d ≠ 0)



theorem wis_take_filter {α : Type*} (p : α → Bool) (L : List α) (k : ℕ) :
    ∃ j ≤ L.length, (L.filter p).take k = (L.take j).filter p := by
  induction L generalizing k with
  | nil => exact ⟨0, le_refl 0, by simp⟩
  | cons a t ih =>
    by_cases hp : p a
    · cases k with
      | zero => exact ⟨0, by simp, by simp⟩
      | succ k' =>
        obtain ⟨j, hj, hje⟩ := ih k'
        refine ⟨j + 1, by simpa using hj, ?_⟩
        rw [List.filter_cons_of_pos hp, List.take_succ_cons, List.take_succ_cons,
          List.filter_cons_of_pos hp, hje]
    · obtain ⟨j, hj, hje⟩ := ih k
      refine ⟨j + 1, by simpa using hj, ?_⟩
      rw [List.filter_cons_of_neg hp, List.take_succ_cons, List.filter_cons_of_neg hp, hje]



theorem wis_take_nonzeroDiffs (f : ℕ → ℤ) (n k : ℕ) :
    ∃ m ≤ n, (wis_nonzeroDiffs f n).take k = wis_nonzeroDiffs f m := by
  unfold wis_nonzeroDiffs
  obtain ⟨j, hj, hje⟩ := wis_take_filter (fun d => decide (d ≠ 0))
    ((List.range n).map (fun i => f (i + 1) - f i)) k
  rw [List.length_map, List.length_range] at hj
  refine ⟨j, hj, ?_⟩
  rw [hje, ← List.map_take, List.take_range, min_eq_left hj]





theorem wis_nonzeroDiffs_sum (f : ℕ → ℤ) (h0 : f 0 = 0) (n : ℕ) :
    (wis_nonzeroDiffs f n).sum = f n := by
  unfold wis_nonzeroDiffs
  induction n with
  | zero => simp [h0]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil]
    by_cases hd : f (k + 1) - f k = 0
    · rw [List.filter_cons_of_neg (by simp [hd]), List.filter_nil]
      simp only [List.sum_nil, add_zero]; omega
    · rw [List.filter_cons_of_pos (by simp [hd]), List.filter_nil]
      simp only [List.sum_cons, List.sum_nil, add_zero]; ring







theorem wis_nonzeroDiffs_isIndicatorStep (f : ℕ → ℤ)
    (h01 : ∀ n, f n = 0 ∨ f n = 1) (h0 : f 0 = 0) (n : ℕ) :
    ∃ ind : ℕ → ℤ,
      (∀ e ∈ wis_nonzeroDiffs f n, e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧
      (∀ m, ind m = 0 ∨ ind m = 1) ∧
      wis_nonzeroDiffs f n =
        (List.range (wis_nonzeroDiffs f n).length).map (fun i => ind (i + 1) - ind i) := by
  set D := wis_nonzeroDiffs f n with hD
  
  have hpm : ∀ e ∈ D, e = 1 ∨ e = -1 := by
    intro e he
    rw [hD, wis_nonzeroDiffs, List.mem_filter] at he
    obtain ⟨hmem, hne⟩ := he
    rw [List.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    have := h01 (i + 1); have := h01 i
    simp only [ne_eq, decide_eq_true_eq] at hne
    omega
  
  
  
  refine ⟨fun k => (D.take k).sum, hpm, by simp, ?_, ?_⟩
  · 
    
    intro k
    
    
    
    
    
    have hprefix : ∃ m ≤ n, D.take k = wis_nonzeroDiffs f m := by
      rcases Nat.lt_or_ge k D.length with hlt | hge
      · 
        
        
        exact wis_take_nonzeroDiffs f n k
      · exact ⟨n, le_refl n, by rw [List.take_of_length_le hge]⟩
    obtain ⟨m, _, hm⟩ := hprefix
    show (D.take k).sum = 0 ∨ (D.take k).sum = 1
    rw [hm, wis_nonzeroDiffs_sum f h0 m]
    exact h01 m
  · 
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.length_map, List.length_range] at h2
      simp only [List.getElem_map, List.getElem_range]
      show D[i] = (D.take (i + 1)).sum - (D.take i).sum
      have hkey : (D.take (i + 1)).sum - (D.take i).sum = D[i] := by
        rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem h2]
        simp
      omega



















noncomputable def wis_indSeq (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c₀ : ℤ) (i : ℕ) : ℤ :=
  wis_ind z Vc (c₀ + (i : ℤ))

theorem wis_indSeq_in_01 (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c₀ : ℤ) (i : ℕ) : wis_indSeq z Vc c₀ i = 0 ∨ wis_indSeq z Vc c₀ i = 1 :=
  wis_ind_in_01 z Vc _




theorem wis_nonzeroDiffs_neg_isIndicatorStep (f : ℕ → ℤ)
    (h01 : ∀ n, f n = 0 ∨ f n = 1) (h0 : f 0 = 0) (n : ℕ) :
    ∃ ind : ℕ → ℤ,
      (∀ e ∈ wis_nonzeroDiffs (fun i => - f i) n, e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧
      (∀ m, ind m = 0 ∨ ind m = -1) ∧
      wis_nonzeroDiffs (fun i => - f i) n =
        (List.range (wis_nonzeroDiffs (fun i => - f i) n).length).map
          (fun i => ind (i + 1) - ind i) := by
  have h01' : ∀ m, (fun i => - f i) m = 0 ∨ (fun i => - f i) m = -1 := by
    intro m; rcases h01 m with h | h <;> simp [h]
  have h0' : (fun i => - f i) 0 = 0 := by simp [h0]
  
  
  set D := wis_nonzeroDiffs (fun i => - f i) n with hD
  have hpm : ∀ e ∈ D, e = 1 ∨ e = -1 := by
    intro e he
    rw [hD, wis_nonzeroDiffs, List.mem_filter] at he
    obtain ⟨hmem, hne⟩ := he
    rw [List.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    have := h01 (i + 1); have := h01 i
    simp only [ne_eq, decide_eq_true_eq] at hne ⊢
    omega
  refine ⟨fun k => (D.take k).sum, hpm, by simp, ?_, ?_⟩
  · intro k
    have hprefix : ∃ m ≤ n, D.take k = wis_nonzeroDiffs (fun i => - f i) m := by
      rcases Nat.lt_or_ge k D.length with _ | hge
      · exact wis_take_nonzeroDiffs (fun i => - f i) n k
      · exact ⟨n, le_refl n, by rw [List.take_of_length_le hge]⟩
    obtain ⟨m, _, hm⟩ := hprefix
    show (D.take k).sum = 0 ∨ (D.take k).sum = -1
    rw [hm, wis_nonzeroDiffs_sum (fun i => - f i) h0' m]
    rcases h01 m with h | h <;> simp [h]
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.length_map, List.length_range] at h2
      simp only [List.getElem_map, List.getElem_range]
      show D[i] = (D.take (i + 1)).sum - (D.take i).sum
      have hkey : (D.take (i + 1)).sum - (D.take i).sum = D[i] := by
        rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem h2]
        simp
      omega









def wis_SignEqIndicatorJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ (c₀ : ℤ) (N : ℕ),
    wis_indSeq z Vc c₀ 0 = 0 ∧
    ((wis_nonzeroDiffs (wis_indSeq z Vc c₀) N).Perm (wnu_signedList z Vc) ∨
     (wis_nonzeroDiffs (fun i => - wis_indSeq z Vc c₀ i) N).Perm (wnu_signedList z Vc))








theorem wis_indicatorSteps_of_signEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wis_SignEqIndicatorJumps z Vc) :
    wst_IndicatorSteps z Vc := by
  obtain ⟨c₀, N, hbase, hperm⟩ := h
  have h01 : ∀ m, wis_indSeq z Vc c₀ m = 0 ∨ wis_indSeq z Vc c₀ m = 1 :=
    fun m => wis_indSeq_in_01 z Vc c₀ m
  have h0 : wis_indSeq z Vc c₀ 0 = 0 := hbase
  rcases hperm with hp | hp
  · obtain ⟨ind, hpm, hind0, hind01, hstep⟩ :=
      wis_nonzeroDiffs_isIndicatorStep (wis_indSeq z Vc c₀) h01 h0 N
    refine ⟨wis_nonzeroDiffs (wis_indSeq z Vc c₀) N, ind, hp, hpm, hind0, Or.inl hind01, hstep⟩
  · obtain ⟨ind, hpm, hind0, hind0neg, hstep⟩ :=
      wis_nonzeroDiffs_neg_isIndicatorStep (wis_indSeq z Vc c₀) h01 h0 N
    refine ⟨wis_nonzeroDiffs (fun i => - wis_indSeq z Vc c₀ i) N, ind, hp, hpm, hind0,
      Or.inr hind0neg, hstep⟩





theorem wis_columnAlternates_of_signEqJumps (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wis_SignEqIndicatorJumps z Vc) :
    wna_ColumnAlternates z Vc :=
  wst_columnAlternates_of_indicatorSteps z Vc (wis_indicatorSteps_of_signEqJumps z Vc h)









theorem wis_unitSquare_rayCount0 :
    jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop = 0 := by
  unfold wwit_unitSquareLoop
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num


theorem wis_unitSquare_rayCount1 :
    jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop = 1 := by
  unfold wwit_unitSquareLoop
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num






theorem wis_unitSquare_signEqJumps :
    wis_SignEqIndicatorJumps (![1, 1] : Site 2) wwit_unitSquareLoop := by
  have hval0 : wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 0 = 0 := by
    show wis_ind (![1, 1] : Site 2) wwit_unitSquareLoop (0 + ((0 : ℕ) : ℤ)) = 0
    unfold wis_ind
    rw [show ((![1, 1] : Site 2) 1) = 1 from by simp, show ((0 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from by simp,
      wis_unitSquare_rayCount0]
    decide
  have hval1 : wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0 1 = 1 := by
    show wis_ind (![1, 1] : Site 2) wwit_unitSquareLoop (0 + ((1 : ℕ) : ℤ)) = 1
    unfold wis_ind
    rw [show ((![1, 1] : Site 2) 1) = 1 from by simp, show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = 1 from by simp,
      wis_unitSquare_rayCount1]
    decide
  refine ⟨0, 1, hval0, Or.inl ?_⟩
  · 
    rw [wnu_unitSquare_signedList]
    show (wis_nonzeroDiffs (wis_indSeq (![1, 1] : Site 2) wwit_unitSquareLoop 0) 1).Perm [1]
    unfold wis_nonzeroDiffs
    rw [show (List.range 1) = [0] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [hval1, hval0]
    norm_num


theorem wis_Ltromino_rayCount0 :
    jec_rayCount (![0, 1] : Site 2) wnu_LtrominoLoop = 0 := by
  unfold wnu_LtrominoLoop
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num


theorem wis_Ltromino_rayCount1 :
    jec_rayCount (![1, 1] : Site 2) wnu_LtrominoLoop = 1 := by
  unfold wnu_LtrominoLoop
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_num







theorem wis_Ltromino_signEqJumps :
    wis_SignEqIndicatorJumps (![1, 1] : Site 2) wnu_LtrominoLoop := by
  have hval0 : wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 0 = 0 := by
    show wis_ind (![1, 1] : Site 2) wnu_LtrominoLoop (0 + ((0 : ℕ) : ℤ)) = 0
    unfold wis_ind
    rw [show ((![1, 1] : Site 2) 1) = 1 from by simp, show ((0 : ℤ) + ((0 : ℕ) : ℤ)) = 0 from by simp,
      wis_Ltromino_rayCount0]
    decide
  have hval1 : wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 1 = 1 := by
    show wis_ind (![1, 1] : Site 2) wnu_LtrominoLoop (0 + ((1 : ℕ) : ℤ)) = 1
    unfold wis_ind
    rw [show ((![1, 1] : Site 2) 1) = 1 from by simp, show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = 1 from by simp,
      wis_Ltromino_rayCount1]
    decide
  refine ⟨0, 1, hval0, Or.inr ?_⟩
  · rw [wnu_Ltromino_signedList]
    show (wis_nonzeroDiffs (fun i => - wis_indSeq (![1, 1] : Site 2) wnu_LtrominoLoop 0 i) 1).Perm [-1]
    unfold wis_nonzeroDiffs
    rw [show (List.range 1) = [0] from rfl]
    simp only [List.map_cons, List.map_nil]
    rw [hval1, hval0]
    norm_num













theorem wis_doubleSquare_not_signEqJumps :
    ¬ wis_SignEqIndicatorJumps (![1, 1] : Site 2) wnu_doubleSquare := by
  intro h
  exact wst_doubleSquare_not_indicatorSteps (wis_indicatorSteps_of_signEqJumps _ _ h)











def wis_twoToggle : ℕ → ℤ := fun i => if i = 1 ∨ i = 2 then 1 else 0




theorem wis_twoToggle_nonzeroDiffs :
    wis_nonzeroDiffs wis_twoToggle 3 = [1, -1] := by
  unfold wis_nonzeroDiffs wis_twoToggle
  decide




theorem wis_twoToggle_isIndicatorStep :
    ∃ ind : ℕ → ℤ,
      (∀ e ∈ ([1, -1] : List ℤ), e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧
      (∀ m, ind m = 0 ∨ ind m = 1) ∧
      ([1, -1] : List ℤ) = (List.range 2).map (fun i => ind (i + 1) - ind i) := by
  have h := wis_nonzeroDiffs_isIndicatorStep wis_twoToggle
    (fun n => by unfold wis_twoToggle; by_cases h : n = 1 ∨ n = 2 <;> simp [h]) rfl 3
  rw [wis_twoToggle_nonzeroDiffs] at h
  simpa using h



theorem wis_twoToggle_alternates : wnu_Alt ([1, -1] : List ℤ) := by
  refine ⟨Or.inl rfl, by norm_num, ?_⟩
  exact Or.inr rfl














































end Lattice

end StatMech
