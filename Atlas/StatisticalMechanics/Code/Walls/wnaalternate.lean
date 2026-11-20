/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.GaussBonnet
import Code.Lattice.CrossingParity
import Code.Lattice.WindingWitness
import Code.Walls.umffullrev
import Code.Walls.wndwinding
import Code.Walls.wnuupperhalf

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice




theorem wna_altSum_abs_le_one (L : List ℤ) (h : wnu_Alt L) : |L.sum| ≤ 1 :=
  wnu_altSum_abs_le_one L h



















def wna_prefixSums (L : List ℤ) : List ℤ :=
  (L.scanl (· + ·) 0).tail





theorem wna_alt_of_prefix_in_01 :
    ∀ (L : List ℤ) (s : ℤ), (s = 0 ∨ s = 1) →
      (∀ x ∈ L, x = 1 ∨ x = -1) →
      (∀ p ∈ (L.scanl (· + ·) s), p = 0 ∨ p = 1) →
      wnu_Alt L := by
  intro L
  induction L with
  | nil => intro s _ _ _; exact trivial
  | cons a t ih =>
    intro s hs hpm hall
    have ha0 : a = 1 ∨ a = -1 := hpm a (by simp)
    have hscan : (a :: t).scanl (· + ·) s = s :: t.scanl (· + ·) (s + a) :=
      List.scanl_cons
    
    have hsa_in : (s + a) = 0 ∨ (s + a) = 1 := by
      apply hall
      rw [hscan]
      refine List.mem_cons_of_mem _ ?_
      cases t with
      | nil => rw [List.scanl_nil]; simp
      | cons b t' => rw [List.scanl_cons]; simp
    cases t with
    | nil => exact ha0
    | cons b t' =>
      have hb0 : b = 1 ∨ b = -1 := hpm b (by simp)
      refine ⟨ha0, ?_, ?_⟩
      · 
        have hsab_in : (s + a + b) = 0 ∨ (s + a + b) = 1 := by
          apply hall
          rw [hscan, List.scanl_cons]
          refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          cases t' with
          | nil => rw [List.scanl_nil]; simp
          | cons c t'' => rw [List.scanl_cons]; simp
        rcases hsa_in with h | h <;> rcases hsab_in with h' | h' <;>
          rcases ha0 with ha | ha <;> rcases hb0 with hb | hb <;> omega
      · 
        apply ih (s + a) hsa_in
        · intro x hx; exact hpm x (by simp [hx])
        · intro p hp
          apply hall
          rw [hscan]
          exact List.mem_cons_of_mem _ hp





theorem wna_alt_of_prefixSums_in_01 (L : List ℤ)
    (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
    (hpref : ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = 1) :
    wnu_Alt L := by
  apply wna_alt_of_prefix_in_01 L 0 (Or.inl rfl) hpm
  intro p hp
  
  rw [show L.scanl (· + ·) 0 = 0 :: wna_prefixSums L from ?_] at hp
  · rcases List.mem_cons.mp hp with h | h
    · left; exact h
    · exact hpref p h
  · unfold wna_prefixSums
    cases L with
    | nil => simp
    | cons a t => rw [List.scanl_cons]; simp














def wna_ColumnAlternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : Prop :=
  ∃ M : List ℤ, M.Perm (wnu_signedList z w) ∧ wnu_Alt M





theorem wna_signedCross_abs_le_one_of_columnAlternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wna_ColumnAlternates z w) :
    |wnd_signedCross z w| ≤ 1 := by
  obtain ⟨M, hperm, halt⟩ := h
  have hsum : M.sum = wnd_signedCross z w := by
    rw [hperm.sum_eq]; exact wnu_signedList_sum z w
  rw [← hsum]
  exact wnu_altSum_abs_le_one M halt




theorem wna_signedCross_pm_one_of_columnAlternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wna_ColumnAlternates z w)
    (hodd : ¬ Even (jec_rayCount z w)) :
    wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 := by
  obtain ⟨M, hperm, halt⟩ := h
  have hsum : M.sum = wnd_signedCross z w := by
    rw [hperm.sum_eq]; exact wnu_signedList_sum z w
  have hne : M.sum ≠ 0 := by
    rw [hsum]; exact wnd_signedCross_ne_zero_of_rayCount_odd z w hodd
  rw [← hsum]
  exact wnu_altSum_pm_one_of_ne_zero M halt hne








theorem wna_alternates_of_signedList_alt (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wnu_Alt (wnu_signedList z w)) :
    wnu_Alternates z w := h


theorem wna_alternates_of_columnAlternates_id (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (h : wnu_Alt (wnu_signedList z w)) :
    wna_ColumnAlternates z w :=
  ⟨wnu_signedList z w, List.Perm.refl _, h⟩









theorem wna_unitSquare_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop :=
  wna_alternates_of_columnAlternates_id _ _ wnu_unitSquare_alternates


theorem wna_unitSquare_signedCross_abs_le_one :
    |wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop| ≤ 1 :=
  wna_signedCross_abs_le_one_of_columnAlternates _ _ wna_unitSquare_columnAlternates



theorem wna_Ltromino_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop :=
  wna_alternates_of_columnAlternates_id _ _ wnu_Ltromino_alternates


theorem wna_Ltromino_signedCross_abs_le_one :
    |wnd_signedCross (![1, 1] : Site 2) wnu_LtrominoLoop| ≤ 1 :=
  wna_signedCross_abs_le_one_of_columnAlternates _ _ wna_Ltromino_columnAlternates





theorem wna_toggle_on_singleton :
    wnu_Alt [(1 : ℤ)] := by
  apply wna_alt_of_prefixSums_in_01
  · intro x hx; simp at hx; omega
  · intro p hp; unfold wna_prefixSums at hp; simp at hp; omega










theorem wna_doubleSquare_not_columnAlternates :
    ¬ wna_ColumnAlternates (![1, 1] : Site 2) wnu_doubleSquare := by
  rintro ⟨M, hperm, halt⟩
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
      have ha := hmem a (by simp)
      have hb := hmem b (by simp)
      rw [ha, hb]
  rw [hM] at halt
  exact wnu_not_alt_oneOne halt




theorem wna_doubleSquare_prefix_leaves_01 :
    ∃ p ∈ wna_prefixSums [(1 : ℤ), 1], ¬ (p = 0 ∨ p = 1) := by
  refine ⟨2, ?_, by omega⟩
  unfold wna_prefixSums; simp












theorem wna_signedCrossPMone_of_columnAlternates (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    wnd_SignedCrossPMone K hK a z := by
  unfold wnd_SignedCrossPMone
  exact wna_signedCross_pm_one_of_columnAlternates z (olb_orbitLoop K hK a.1 a.2) halt hodd



theorem wna_revCount_pm_one_of_columnAlternates_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wnd_revCount_pm_one_of_residues K hK a z hbridge
    (wna_signedCrossPMone_of_columnAlternates K hK a z halt hodd)





theorem wna_eulerCharOne_of_columnAlternates_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hp : 3 ≤ dartOrbitPeriod K a)
    (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    EulerCharOne K a :=
  wnd_eulerCharOne_of_residues K hK a z hp hbridge
    (wna_signedCrossPMone_of_columnAlternates K hK a z halt hodd)



























































end Lattice

end StatMech
