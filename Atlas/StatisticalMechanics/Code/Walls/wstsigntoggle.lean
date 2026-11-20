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

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice












theorem wst_prefixSum_telescope (ind : ℕ → ℤ) :
    ∀ n : ℕ, ((List.range n).map (fun i => ind (i + 1) - ind i)).sum = ind n - ind 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring






theorem wst_prefixSums_in_01_of_indicatorSteps (ind : ℕ → ℤ)
    (h01 : ∀ n, ind n = 0 ∨ ind n = 1) (h0 : ind 0 = 0) (n : ℕ) :
    ∀ p ∈ wna_prefixSums ((List.range n).map (fun i => ind (i + 1) - ind i)),
      p = 0 ∨ p = 1 := by
  intro p hp
  
  
  
  
  obtain ⟨k, hk, hpk⟩ : ∃ k, k ≤ n ∧
      p = ((List.range k).map (fun i => ind (i + 1) - ind i)).sum := by
    
    unfold wna_prefixSums at hp
    have hmem := List.mem_of_mem_tail hp
    
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨j, hj, hjeq⟩ := hmem
    
    have hjlt : j ≤ n := by
      rw [List.length_scanl, List.length_map, List.length_range] at hj; omega
    refine ⟨j, hjlt, ?_⟩
    rw [← hjeq, List.getElem_scanl]
    
    have htake : ((List.range n).map (fun i => ind (i + 1) - ind i)).take j
        = (List.range j).map (fun i => ind (i + 1) - ind i) := by
      rw [← List.map_take, List.take_range, min_eq_left hjlt]
    rw [htake, ← List.sum_eq_foldl]
  rw [hpk, wst_prefixSum_telescope ind k, h0, sub_zero]
  exact h01 k




theorem wst_prefixSums_in_01_of_toggle (L : List ℤ) (ind : ℕ → ℤ)
    (h01 : ∀ n, ind n = 0 ∨ ind n = 1) (h0 : ind 0 = 0)
    (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
    ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = 1 := by
  intro p hp
  rw [hL] at hp
  exact wst_prefixSums_in_01_of_indicatorSteps ind h01 h0 L.length p hp













theorem wst_alt_of_indicatorSteps (L : List ℤ) (ind : ℕ → ℤ)
    (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
    (h01 : ∀ n, ind n = 0 ∨ ind n = 1) (h0 : ind 0 = 0)
    (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
    wnu_Alt L :=
  wna_alt_of_prefixSums_in_01 L hpm (wst_prefixSums_in_01_of_toggle L ind h01 h0 hL)












theorem wst_alt_map_neg : ∀ L : List ℤ, wnu_Alt L → wnu_Alt (L.map (fun x => -x))
  | [], _ => trivial
  | [a], h => by simp only [List.map_cons, List.map_nil]; rcases h with h | h <;> simp [h]
  | a :: b :: t, h => by
      obtain ⟨ha, hb, ht⟩ := wnu_Alt_cons_cons.mp h
      have htail : wnu_Alt ((b :: t).map (fun x => -x)) := wst_alt_map_neg (b :: t) ht
      simp only [List.map_cons] at htail ⊢
      refine ⟨?_, ?_, htail⟩
      · rcases ha with h | h <;> simp [h]
      · subst hb; ring





theorem wst_alt_of_prefixSums_in_0neg (L : List ℤ)
    (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
    (hpref : ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = -1) :
    wnu_Alt L := by
  
  set Lneg := L.map (fun x => -x) with hLneg
  have hpmneg : ∀ x ∈ Lneg, x = 1 ∨ x = -1 := by
    intro x hx
    rw [hLneg, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rcases hpm a ha with h | h <;> simp [h]
  
  have hprefneg_eq : wna_prefixSums Lneg = (wna_prefixSums L).map (fun x => -x) := by
    unfold wna_prefixSums
    rw [hLneg]
    
    have hscan : ∀ (s : ℤ) (M : List ℤ),
        (M.map (fun x => -x)).scanl (· + ·) (-s) = (M.scanl (· + ·) s).map (fun x => -x) := by
      intro s M
      induction M generalizing s with
      | nil => simp
      | cons a t ih =>
        rw [List.map_cons, List.scanl_cons, List.scanl_cons, List.map_cons]
        congr 1
        rw [show -s + -a = -(s + a) from by ring, ih (s + a)]
    have := hscan 0 L
    simp only [neg_zero] at this
    rw [this, ← List.map_tail]
  have hprefneg : ∀ p ∈ wna_prefixSums Lneg, p = 0 ∨ p = 1 := by
    intro p hp
    rw [hprefneg_eq, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rcases hpref q hq with h | h <;> simp [h]
  have haltneg : wnu_Alt Lneg := wna_alt_of_prefixSums_in_01 Lneg hpmneg hprefneg
  
  have hLL : L = Lneg.map (fun x => -x) := by
    rw [hLneg, List.map_map]; simp
  rw [hLL]
  exact wst_alt_map_neg Lneg haltneg





theorem wst_alt_of_indicatorSteps_neg (L : List ℤ) (ind : ℕ → ℤ)
    (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
    (h0neg : ∀ n, ind n = 0 ∨ ind n = -1) (h0 : ind 0 = 0)
    (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
    wnu_Alt L := by
  apply wst_alt_of_prefixSums_in_0neg L hpm
  intro p hp
  
  obtain ⟨k, hpk⟩ : ∃ k, p = ind k := by
    unfold wna_prefixSums at hp
    have hmem := List.mem_of_mem_tail hp
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨j, hj, hjeq⟩ := hmem
    have hjlt : j ≤ L.length := by
      rw [List.length_scanl] at hj; omega
    refine ⟨j, ?_⟩
    rw [← hjeq, List.getElem_scanl]
    
    have htake : L.take j = (List.range j).map (fun i => ind (i + 1) - ind i) := by
      conv_lhs => rw [hL]
      rw [← List.map_take, List.take_range, min_eq_left hjlt]
    rw [htake, ← List.sum_eq_foldl, wst_prefixSum_telescope ind j, h0, sub_zero]
  rw [hpk]; exact h0neg k




















def wst_IndicatorSteps (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : Prop :=
  ∃ (M : List ℤ) (ind : ℕ → ℤ),
    M.Perm (wnu_signedList z w) ∧
    (∀ e ∈ M, e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧
    ((∀ n, ind n = 0 ∨ ind n = 1) ∨ (∀ n, ind n = 0 ∨ ind n = -1)) ∧
    M = (List.range M.length).map (fun i => ind (i + 1) - ind i)






theorem wst_columnAlternates_of_indicatorSteps (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wst_IndicatorSteps z w) :
    wna_ColumnAlternates z w := by
  obtain ⟨M, ind, hperm, hpm, h0, hor, hL⟩ := h
  refine ⟨M, hperm, ?_⟩
  rcases hor with h01 | h0neg
  · exact wst_alt_of_indicatorSteps M ind hpm h01 h0 hL
  · exact wst_alt_of_indicatorSteps_neg M ind hpm h0neg h0 hL











theorem wst_signedCrossPMone_of_indicatorSteps (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    wnd_SignedCrossPMone K hK a z :=
  wna_signedCrossPMone_of_columnAlternates K hK a z
    (wst_columnAlternates_of_indicatorSteps z (olb_orbitLoop K hK a.1 a.2) hstep) hodd




theorem wst_revCount_pm_one_of_indicatorSteps_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wna_revCount_pm_one_of_columnAlternates_bridge K hK a z
    (wst_columnAlternates_of_indicatorSteps z (olb_orbitLoop K hK a.1 a.2) hstep) hodd hbridge





theorem wst_eulerCharOne_of_indicatorSteps_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    EulerCharOne K a :=
  wna_eulerCharOne_of_columnAlternates_bridge K hK a z hp
    (wst_columnAlternates_of_indicatorSteps z (olb_orbitLoop K hK a.1 a.2) hstep) hodd hbridge











theorem wst_unitSquare_indicatorSteps :
    wst_IndicatorSteps (![1, 1] : Site 2) wwit_unitSquareLoop := by
  refine ⟨[1], (fun n => if n = 0 then 0 else 1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [wnu_unitSquare_signedList]
  · intro e he; simp at he; omega
  · simp
  · left; intro n; by_cases h : n = 0 <;> simp [h]
  · decide





theorem wst_Ltromino_indicatorSteps :
    wst_IndicatorSteps (![1, 1] : Site 2) wnu_LtrominoLoop := by
  refine ⟨[-1], (fun n => if n = 0 then 0 else -1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [wnu_Ltromino_signedList]
  · intro e he; simp at he; omega
  · simp
  · right; intro n; by_cases h : n = 0 <;> simp [h]
  · decide




theorem wst_unitSquare_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop :=
  wst_columnAlternates_of_indicatorSteps _ _ wst_unitSquare_indicatorSteps


theorem wst_Ltromino_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop :=
  wst_columnAlternates_of_indicatorSteps _ _ wst_Ltromino_indicatorSteps












theorem wst_doubleSquare_not_indicatorSteps :
    ¬ wst_IndicatorSteps (![1, 1] : Site 2) wnu_doubleSquare := by
  rintro ⟨M, ind, hperm, hpm, h0, hor, hL⟩
  rw [wnu_doubleSquare_signedList] at hperm
  
  have hM : M = [1, 1] := by
    have hlen := hperm.length_eq
    have hmem : ∀ x ∈ M, x = 1 := by
      intro x hx
      have hx2 := hperm.mem_iff.mp hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2
      rcases hx2 with h | h <;> exact h
    match M, hlen with
    | [a, b], _ =>
      have ha := hmem a (by simp); have hb := hmem b (by simp)
      rw [ha, hb]
  
  rw [hM] at hL
  simp only [List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.map_append, List.map_cons, List.map_nil, List.nil_append] at hL
  
  have h1 : ind 1 - ind 0 = 1 := by
    have := congrArg (fun l => l[0]?) hL; simpa using this.symm
  have h2 : ind 2 - ind 1 = 1 := by
    have := congrArg (fun l => l[1]?) hL; simpa using this.symm
  have hind2 : ind 2 = 2 := by rw [h0] at h1; omega
  rcases hor with h | h <;> rcases h 2 with h' | h' <;> omega




theorem wst_doubleSquare_prefix_leaves_twoState :
    ∃ p ∈ wna_prefixSums [(1 : ℤ), 1], ¬ (p = 0 ∨ p = 1) ∧ ¬ (p = 0 ∨ p = -1) := by
  refine ⟨2, ?_, by omega, by omega⟩
  unfold wna_prefixSums; simp













































end Lattice

end StatMech
