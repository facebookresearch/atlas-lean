/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Walls.jc_core
import Code.Walls.jc_earanchor

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice










noncomputable def jc2_rightEnd (c : Site 2) (len : ℤ) : Site 2 := c + ![len, 0]



theorem jc2_rightEnd_mem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) : jc2_rightEnd c len ∈ K :=
  hrun.run_mem len hrun.len_nonneg (le_refl len)
















theorem jc2_thin_pendant (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) (hlen : 1 ≤ len)
    (hthin : jc2_rightEnd c len + ![0, -1] ∉ K) :
    jc_IsPendantCell K (jc2_rightEnd c len) :=
  jc_rightEnd_pendant_of_down_nmem K c len hrun hlen hthin












theorem jc2_left_down_distinct (c : Site 2) (len : ℤ) :
    (c + ![len - 1, 0] : Site 2) ≠ jc2_rightEnd c len + ![0, -1] := by
  intro h
  have hy : (c + ![len - 1, 0] : Site 2) 1 = (jc2_rightEnd c len + ![0, -1] : Site 2) 1 := by
    rw [h]
  rw [jc2_rightEnd] at hy
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at hy
  omega








theorem jc2_thick_not_pendant (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) (hlen : 1 ≤ len)
    (hthick : jc2_rightEnd c len + ![0, -1] ∈ K) :
    ¬ jc_IsPendantCell K (jc2_rightEnd c len) := by
  rw [jc2_rightEnd] at hthick ⊢
  set r : Site 2 := c + ![len, 0] with hr
  rintro ⟨_, u, ⟨_, _⟩, huniq⟩
  
  have hleftK : (c + ![len - 1, 0] : Site 2) ∈ K :=
    hrun.run_mem (len - 1) (by omega) (by omega)
  have hleftAdj : (hypercubicLattice 2).Adj r (c + ![len - 1, 0]) := by
    rw [hr, hypercubicLattice_adj, Fin.sum_univ_two]
    have e0 : ((c + ![len, 0] : Site 2) 0 - (c + ![len - 1, 0] : Site 2) 0) = 1 := by
      simp only [Pi.add_apply, Matrix.cons_val_zero]; ring
    have e1 : ((c + ![len, 0] : Site 2) 1 - (c + ![len - 1, 0] : Site 2) 1) = 0 := by
      simp only [Pi.add_apply, Matrix.cons_val_one]; ring
    rw [e0, e1]; decide
  
  have hdownAdj : (hypercubicLattice 2).Adj r (r + ![0, -1]) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    have e0 : (r 0 - (r + ![0, -1] : Site 2) 0) = 0 := by
      simp only [Pi.add_apply, Matrix.cons_val_zero]; ring
    have e1 : (r 1 - (r + ![0, -1] : Site 2) 1) = 1 := by
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
    rw [e0, e1]; decide
  
  have h1 : (c + ![len - 1, 0] : Site 2) = u := huniq _ ⟨hleftK, hleftAdj⟩
  have h2 : (r + ![0, -1] : Site 2) = u := huniq _ ⟨hthick, hdownAdj⟩
  apply jc2_left_down_distinct c len
  rw [jc2_rightEnd, ← hr, h1, h2]




















theorem jc2_thin_thick_dichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) (hlen : 1 ≤ len) :
    (jc2_rightEnd c len + ![0, -1] ∉ K ∧ jc_IsPendantCell K (jc2_rightEnd c len)) ∨
      (jc2_rightEnd c len + ![0, -1] ∈ K ∧ ¬ jc_IsPendantCell K (jc2_rightEnd c len)) := by
  rcases em (jc2_rightEnd c len + ![0, -1] ∈ K) with hin | hout
  · exact Or.inr ⟨hin, jc2_thick_not_pendant K c len hrun hlen hin⟩
  · exact Or.inl ⟨hout, jc2_thin_pendant K c len hrun hlen hout⟩










theorem jc2_rightEnd_len_zero (c : Site 2) : jc2_rightEnd c 0 = c := by
  rw [jc2_rightEnd]
  funext i; fin_cases i <;> simp [Pi.add_apply]








theorem jc2_len_zero_right_or_down (K : Set (Site 2)) (c : Site 2)
    (hrun : jc_IsTopRowRun K c 0) (v : Site 2) (hv : v ∈ K)
    (hadj : (hypercubicLattice 2).Adj v c) :
    v = jc2_rightEnd c 0 + ![1, 0] ∨ v = jc2_rightEnd c 0 + ![0, -1] := by
  rw [jc2_rightEnd_len_zero]
  exact jc_extremeCell_neighbor_right_or_down K c v hrun.isExtreme hv hadj
















structure jc2_ThinThickDichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop where
  

  dichotomy : 1 ≤ len →
    (jc2_rightEnd c len + ![0, -1] ∉ K ∧ jc_IsPendantCell K (jc2_rightEnd c len)) ∨
      (jc2_rightEnd c len + ![0, -1] ∈ K ∧ ¬ jc_IsPendantCell K (jc2_rightEnd c len))
  

  len_zero_split : len = 0 → ∀ v ∈ K, (hypercubicLattice 2).Adj v c →
    v = jc2_rightEnd c len + ![1, 0] ∨ v = jc2_rightEnd c len + ![0, -1]




theorem jc2_topRowRun_thinThickDichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) : jc2_ThinThickDichotomy K c len where
  dichotomy hlen := jc2_thin_thick_dichotomy K c len hrun hlen
  len_zero_split h0 v hv hadj := by
    subst h0
    exact jc2_len_zero_right_or_down K c hrun v hv hadj










theorem jc2_thinThickDichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) : jc2_ThinThickDichotomy K c len :=
  jc2_topRowRun_thinThickDichotomy K c len hrun











theorem jc2_domino_thin_pendant :
    jc_IsPendantCell domino (jc2_rightEnd (![0, 0] : Site 2) 1) := by
  apply jc2_thin_pendant domino (![0, 0] : Site 2) 1 jc_domino_isTopRowRun (by norm_num)
  rw [jc2_rightEnd]
  apply not_mem_domino
  intro h
  rcases h with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    · revert h1
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega





theorem jc2_unitCell_len_zero_split :
    jc2_ThinThickDichotomy unitCell (![0, 0] : Site 2) 0 :=
  jc2_thinThickDichotomy unitCell (![0, 0]) 0 jc_unitCell_isTopRowRun

end Walls

end StatMech
