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

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice

open StatMech.Walls










def wos_SignsAlternateInColumnOrder (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : Prop :=
  wnu_Alt (wcb_columnSorted z w)








theorem wos_signsAlternate_columnAlternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wos_SignsAlternateInColumnOrder z w) :
    wna_ColumnAlternates z w :=
  wcb_columnAlternates_of_sorted_alt z w h






theorem wos_signedCross_abs_le_one (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wos_SignsAlternateInColumnOrder z w) :
    |wnd_signedCross z w| ≤ 1 :=
  wna_signedCross_abs_le_one_of_columnAlternates z w (wos_signsAlternate_columnAlternates z w h)






theorem wos_signedCross_pm_one (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wos_SignsAlternateInColumnOrder z w)
    (hodd : ¬ Even (jec_rayCount z w)) :
    wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 :=
  wna_signedCross_pm_one_of_columnAlternates z w (wos_signsAlternate_columnAlternates z w h) hodd











theorem wos_alt_eq_of_len_head {L M : List ℤ} (hL : wnu_Alt L) (hM : wnu_Alt M)
    (hlen : L.length = M.length) (hhead : L.headI = M.headI) : L = M := by
  induction L generalizing M with
  | nil => cases M with
    | nil => rfl
    | cons b t => simp at hlen
  | cons a s ih =>
    cases M with
    | nil => simp at hlen
    | cons b u =>
      simp only [List.headI] at hhead
      subst hhead
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      cases s with
      | nil =>
        cases u with
        | nil => rfl
        | cons => simp at hlen
      | cons s0 s' =>
        cases u with
        | nil => simp at hlen
        | cons u0 u' =>
          
          have hsa := (wnu_Alt_cons_cons.mp hL).2.1   
          have hua := (wnu_Alt_cons_cons.mp hM).2.1   
          have htL : wnu_Alt (s0 :: s') := (wnu_Alt_cons_cons.mp hL).2.2
          have htM : wnu_Alt (u0 :: u') := (wnu_Alt_cons_cons.mp hM).2.2
          have hheadT : (s0 :: s').headI = (u0 :: u').headI := by
            simp only [List.headI]; rw [hsa, hua]
          have := ih (M := u0 :: u') htL htM (by simpa using hlen) hheadT
          rw [this]


theorem wos_alt_map_neg {L : List ℤ} (h : wnu_Alt L) : wnu_Alt (L.map (fun x => -x)) := by
  induction L with
  | nil => simp
  | cons a s ih =>
    cases s with
    | nil =>
      rcases (wnu_Alt_singleton a).mp h with h1 | h1 <;> subst h1 <;> simp
    | cons b t =>
      obtain ⟨ha, hba, htl⟩ := wnu_Alt_cons_cons.mp h
      simp only [List.map_cons]
      rw [wnu_Alt_cons_cons]
      refine ⟨?_, by rw [hba]; try ring, ?_⟩
      · rcases ha with h1 | h1 <;> subst h1 <;> simp
      · have := ih htl
        simpa using this













theorem wos_nonzeroDiffs_head_one (f : ℕ → ℤ)
    (h01 : ∀ n, f n = 0 ∨ f n = 1) (h0 : f 0 = 0) (n : ℕ)
    (hne : wis_nonzeroDiffs f n ≠ []) :
    (wis_nonzeroDiffs f n).headI = 1 := by
  
  
  set D := wis_nonzeroDiffs f n with hD
  obtain ⟨d, t, hdt⟩ := List.exists_cons_of_ne_nil hne
  have hhead : D.headI = d := by rw [hdt]; rfl
  
  have hpm : ∀ e ∈ D, e = 1 ∨ e = -1 := by
    intro e he
    rw [hD, wis_nonzeroDiffs, List.mem_filter] at he
    obtain ⟨hmem, hnee⟩ := he
    rw [List.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    have := h01 (i + 1); have := h01 i
    simp only [ne_eq, decide_eq_true_eq] at hnee
    omega
  have hd_pm : d = 1 ∨ d = -1 := hpm d (by rw [hdt]; exact List.mem_cons_self ..)
  
  have htake : D.take 1 = [d] := by rw [hdt]; rfl
  obtain ⟨m, _, hm⟩ := wis_take_nonzeroDiffs f n 1
  rw [← hD] at hm
  have hsum1 : (D.take 1).sum = f m := by rw [hm, wis_nonzeroDiffs_sum f h0 m]
  rw [htake] at hsum1
  simp only [List.sum_cons, List.sum_nil, add_zero] at hsum1
  have hfm := h01 m
  rw [hhead]
  rcases hd_pm with h | h
  · exact h
  · exfalso; rw [h] at hsum1; omega


theorem wos_indNonzeroDiffs_alternates (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (c₀ : ℤ) (N : ℕ)
    (hbase : wis_indSeq z Vc c₀ 0 = 0) :
    wnu_Alt (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N) := by
  obtain ⟨ind, hpm, hind0, hind01, hstep⟩ :=
    wis_nonzeroDiffs_isIndicatorStep (wis_indSeq z Vc c₀)
      (fun m => wis_indSeq_in_01 z Vc c₀ m) hbase N
  exact wst_alt_of_indicatorSteps _ ind hpm hind01 hind0 hstep




















def wos_IndicatorLenEq (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ (c₀ : ℤ) (N : ℕ), wis_indSeq z Vc c₀ 0 = 0 ∧
    (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N).length = (wcb_columnSorted z Vc).length




theorem wos_nonzeroDiffs_neg (f : ℕ → ℤ) (n : ℕ) :
    wis_nonzeroDiffs (fun i => - f i) n = (wis_nonzeroDiffs f n).map (fun x => -x) := by
  unfold wis_nonzeroDiffs
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.filter_append,
      List.filter_append, List.map_append, ih]
    congr 1
    simp only [List.map_cons, List.map_nil]
    by_cases hd : f (k + 1) - f k = 0
    · have hd' : (fun i => - f i) (k + 1) - (fun i => - f i) k = 0 := by simp only; omega
      rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq, ne_eq, not_not]; exact hd'),
          List.filter_cons_of_neg (by simp only [decide_eq_true_eq, ne_eq, not_not]; exact hd)]
      simp
    · have hd' : (fun i => - f i) (k + 1) - (fun i => - f i) k ≠ 0 := by simp only; omega
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq, ne_eq]; exact hd'),
          List.filter_cons_of_pos (by simp only [decide_eq_true_eq, ne_eq]; exact hd)]
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · show - f (k + 1) - (- f k) = -(f (k + 1) - f k); ring
      · rfl








theorem wos_signEqIndicatorJumps_of_alternate (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (halt : wos_SignsAlternateInColumnOrder z Vc)
    (hlen : wos_IndicatorLenEq z Vc) :
    wis_SignEqIndicatorJumps z Vc := by
  obtain ⟨c₀, N, hbase, hlenEq⟩ := hlen
  set D := wis_nonzeroDiffs (wis_indSeq z Vc c₀) N with hD
  have hDalt : wnu_Alt D := wos_indNonzeroDiffs_alternates z Vc c₀ N hbase
  have hCalt : wnu_Alt (wcb_columnSorted z Vc) := halt
  have hperm : (wcb_columnSorted z Vc).Perm (wnu_signedList z Vc) :=
    wcb_columnOrder_permutes_signedList z Vc
  refine ⟨c₀, N, hbase, ?_⟩
  rw [← hD]
  
  by_cases hlenz : (wcb_columnSorted z Vc).length = 0
  · 
    have hDempty : D = [] := List.length_eq_zero_iff.mp (by rw [hlenEq, hlenz])
    have hCempty : wcb_columnSorted z Vc = [] := List.length_eq_zero_iff.mp hlenz
    left
    rw [hDempty]
    rw [hCempty] at hperm
    exact hperm
  · 
    have hDne : D ≠ [] := by
      intro h; apply hlenz; rw [← hlenEq, h]; simp
    have hCne : wcb_columnSorted z Vc ≠ [] := fun h => hlenz (by rw [h]; simp)
    
    have hDhead : D.headI = 1 :=
      wos_nonzeroDiffs_head_one (wis_indSeq z Vc c₀)
        (fun m => wis_indSeq_in_01 z Vc c₀ m) hbase N hDne
    
    have hChead : (wcb_columnSorted z Vc).headI = 1 ∨ (wcb_columnSorted z Vc).headI = -1 := by
      obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hCne
      have := wnu_Alt_head_pm (hct ▸ hCalt)
      rw [hct]; simpa using this
    rcases hChead with hCp | hCm
    · 
      left
      have hDeqC : D = wcb_columnSorted z Vc :=
        wos_alt_eq_of_len_head hDalt hCalt hlenEq (by rw [hDhead, hCp])
      rw [hDeqC]; exact hperm
    · 
      right
      
      have hnegD : (D.map (fun x => -x)) = wcb_columnSorted z Vc := by
        apply wos_alt_eq_of_len_head (wos_alt_map_neg hDalt) hCalt
        · simp [hlenEq]
        · 
          obtain ⟨d, t, hdt⟩ := List.exists_cons_of_ne_nil hDne
          rw [hdt, List.map_cons]
          simp only [List.headI]
          have hd1 : d = 1 := by rw [← hDhead, hdt]; rfl
          rw [hd1]
          exact hCm.symm
      
      have hDnegList : wis_nonzeroDiffs (fun i => - wis_indSeq z Vc c₀ i) N
          = D.map (fun x => -x) :=
        (wos_nonzeroDiffs_neg (wis_indSeq z Vc c₀) N).trans (by rw [hD])
      rw [hDnegList, hnegD]
      exact hperm









theorem wos_unitSquare_signsAlternate :
    wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wwit_unitSquareLoop := by
  unfold wos_SignsAlternateInColumnOrder
  rw [wcb_unitSquare_columnSorted]
  exact Or.inl rfl



theorem wos_Ltromino_signsAlternate :
    wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wnu_LtrominoLoop := by
  unfold wos_SignsAlternateInColumnOrder
  rw [wcb_Ltromino_columnSorted]
  exact Or.inr rfl


theorem wos_unitSquare_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop :=
  wos_signsAlternate_columnAlternates _ _ wos_unitSquare_signsAlternate


theorem wos_Ltromino_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop :=
  wos_signsAlternate_columnAlternates _ _ wos_Ltromino_signsAlternate









theorem wos_twoToggle_alternates : wnu_Alt ([1, -1] : List ℤ) := by
  refine ⟨Or.inl rfl, by norm_num, ?_⟩
  exact Or.inr rfl


theorem wos_twoToggle_neg_alternates : wnu_Alt ([-1, 1] : List ℤ) := by
  refine ⟨Or.inr rfl, by norm_num, ?_⟩
  exact Or.inl rfl




theorem wos_twoToggle_eq (M : List ℤ) (hM : wnu_Alt M) (hlen : M.length = 2)
    (hhead : M.headI = 1) : M = [1, -1] := by
  have := wos_alt_eq_of_len_head hM wos_twoToggle_alternates (by simp [hlen]) (by simp [hhead])
  exact this











theorem wos_doubleSquare_list_not_alternates : ¬ wnu_Alt ([1, 1] : List ℤ) := by
  intro h
  have := (wnu_Alt_cons_cons.mp h).2.1
  norm_num at this




theorem wos_doubleSquare_not_signsAlternate :
    ¬ wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wnu_doubleSquare := by
  unfold wos_SignsAlternateInColumnOrder
  rw [wcb_doubleSquare_columnSorted]
  exact wos_doubleSquare_list_not_alternates

end Lattice

end StatMech
