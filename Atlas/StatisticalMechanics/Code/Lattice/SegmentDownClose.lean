/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.JordanInteriorLib
import Code.Lattice.RowLinkedClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice















theorem sdc_down_on_support_of_notInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hnot : (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
    (![x, y - 1] : Site 2) ∈ Vc.support := by
  obtain ⟨hzsup, hzint⟩ := (jil_mem_offSupportInterior Vc _).mp hz
  by_contra hdown
  
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x, y - 1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hpar := jec_localConstancy Vc hadj hzsup hdown
  refine hnot ?_
  rw [jil_mem_offSupportInterior]
  refine ⟨hdown, ?_⟩
  rw [jec_mem_leftRegion] at hzint ⊢
  intro h; exact hzint (hpar.mpr h)







theorem sdc_no_segmentDown_of_bottomInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hbot : ∀ t : ℤ, (![t, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
    ¬ ∃ cx : ℤ, x ≤ cx ∧
        (∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support) ∧
        (![cx, y - 1] : Site 2) ∉ Vc.support := by
  rintro ⟨cx, hxcx, hrun, hcdown⟩
  
  
  have hcoff : (![cx, y] : Site 2) ∉ Vc.support := hrun cx hxcx le_rfl
  have hcL : (![cx, y] : Site 2) ∈ jec_leftRegion Vc :=
    jil_hsegment_subset_leftRegion Vc (lo := x) (hi := cx) (y := y)
      (x₀ := x) (x := cx) le_rfl hxcx hxcx le_rfl
      (by intro t ht ht'; exact hrun t ht ht')
      (jil_mem_offSupportInterior Vc _ |>.mp hz).2
  have hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    (jil_mem_offSupportInterior Vc _).mpr ⟨hcoff, hcL⟩
  exact hcdown (sdc_down_on_support_of_notInterior Vc hc (by simpa using hbot cx))













noncomputable def sdc_fjord : (hypercubicLattice 2).Walk ![(0:ℤ),(0:ℤ)] ![(0:ℤ),(0:ℤ)] :=
  let s1 : (hypercubicLattice 2).Walk ![(0:ℤ),0] ![3,0] :=
    (jec_hsegRight 0 0 3).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![(3:ℤ),0] ![3,3] :=
    (jec_vsegUp 3 0 3).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![(3:ℤ),3] ![4,3] :=
    (jec_hsegRight 3 3 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s4 : (hypercubicLattice 2).Walk ![(4:ℤ),3] ![4,0] :=
    ((jec_vsegUp 4 0 3).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s5 : (hypercubicLattice 2).Walk ![(4:ℤ),0] ![7,0] :=
    (jec_hsegRight 0 4 3).copy rfl (by ext i; fin_cases i <;> simp)
  let s6 : (hypercubicLattice 2).Walk ![(7:ℤ),0] ![7,4] :=
    (jec_vsegUp 7 0 4).copy rfl (by ext i; fin_cases i <;> simp)
  let s7 : (hypercubicLattice 2).Walk ![(7:ℤ),4] ![0,4] :=
    ((jec_hsegRight 4 0 7).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s8 : (hypercubicLattice 2).Walk ![(0:ℤ),4] ![0,0] :=
    ((jec_vsegUp 0 0 4).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append s8))))))





theorem sdc_fjord_raycount (z : Site 2) :
    jec_rayCount z sdc_fjord =
      (if 3 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (3:ℤ) - 1 then 1 else 0)
      + (if 4 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (3:ℤ) - 1 then 1 else 0)
      + (if 7 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (4:ℤ) - 1 then 1 else 0)
      + (if 0 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (4:ℤ) - 1 then 1 else 0) := by
  unfold sdc_fjord
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight]
  push_cast; ring_nf





theorem sdc_hsegRight_mem (row : ℤ) : ∀ (k j : ℕ), ∀ (t : ℤ), j ≤ k →
    (![t + (j:ℤ), row] : Site 2) ∈ (jec_hsegRight row t k).support := by
  intro k
  induction k with
  | zero =>
    intro j t hj; have : j = 0 := by omega
    subst this
    rw [jec_hsegRight, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil]; simp
  | succ k ih =>
    intro j t hj
    rw [jec_hsegRight, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; simp
    · right
      have hh := ih (j - 1) (t + 1) (by omega)
      have heq : (![t + (j:ℤ), row] : Site 2) = (![(t + 1) + ((j - 1 : ℕ):ℤ), row] : Site 2) := by
        ext i; fin_cases i <;> simp; omega
      rw [heq]; exact hh



theorem sdc_vsegUp_mem (col : ℤ) : ∀ (k j : ℕ), ∀ (r : ℤ), j ≤ k →
    (![col, r + (j:ℤ)] : Site 2) ∈ (jec_vsegUp col r k).support := by
  intro k
  induction k with
  | zero =>
    intro j r hj; have : j = 0 := by omega
    subst this
    rw [jec_vsegUp, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil]; simp
  | succ k ih =>
    intro j r hj
    rw [jec_vsegUp, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; simp
    · right
      have hh := ih (j - 1) (r + 1) (by omega)
      have heq : (![col, r + (j:ℤ)] : Site 2) = (![col, (r + 1) + ((j - 1 : ℕ):ℤ)] : Site 2) := by
        ext i; fin_cases i <;> simp; omega
      rw [heq]; exact hh


theorem sdc_hsegRight_mem' (row t : ℤ) (k : ℕ) (c : ℤ) (h1 : t ≤ c) (h2 : c ≤ t + (k:ℤ)) :
    (![c, row] : Site 2) ∈ (jec_hsegRight row t k).support := by
  have hh := sdc_hsegRight_mem row k (c - t).toNat t (by omega)
  have heq : (![t + ((c - t).toNat : ℤ), row] : Site 2) = (![c, row] : Site 2) := by
    ext i; fin_cases i <;> simp; omega
  rwa [heq] at hh


theorem sdc_vsegUp_mem' (col r : ℤ) (k : ℕ) (c : ℤ) (h1 : r ≤ c) (h2 : c ≤ r + (k:ℤ)) :
    (![col, c] : Site 2) ∈ (jec_vsegUp col r k).support := by
  have hh := sdc_vsegUp_mem col k (c - r).toNat r (by omega)
  have heq : (![col, r + ((c - r).toNat : ℤ)] : Site 2) = (![col, c] : Site 2) := by
    ext i; fin_cases i <;> simp; omega
  rwa [heq] at hh



theorem sdc_fjord_support_locus (p : Site 2) (hp : p ∈ sdc_fjord.support) :
      (p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ 3) ∨
      (p 0 = 3 ∧ 0 ≤ p 1 ∧ p 1 ≤ 3) ∨
      (p 1 = 3 ∧ 3 ≤ p 0 ∧ p 0 ≤ 4) ∨
      (p 0 = 4 ∧ 0 ≤ p 1 ∧ p 1 ≤ 3) ∨
      (p 1 = 0 ∧ 4 ≤ p 0 ∧ p 0 ≤ 7) ∨
      (p 0 = 7 ∧ 0 ≤ p 1 ∧ p 1 ≤ 4) ∨
      (p 1 = 4 ∧ 0 ≤ p 0 ∧ p 0 ≤ 7) ∨
      (p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 4) := by
  unfold sdc_fjord at hp
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
  rcases hp with h|h|h|h|h|h|h|h
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 0 0 3 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 3 0 3 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 3 3 1 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 4 0 3 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 0 4 3 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 7 0 4 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 4 0 7 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 0 0 4 h; push_cast at *; omega




theorem sdc_fjord_off_51 : (![5, 1] : Site 2) ∉ sdc_fjord.support := by
  intro h; have := sdc_fjord_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; omega


theorem sdc_fjord_off_61 : (![6, 1] : Site 2) ∉ sdc_fjord.support := by
  intro h; have := sdc_fjord_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; omega


theorem sdc_fjord_off_11 : (![1, 1] : Site 2) ∉ sdc_fjord.support := by
  intro h; have := sdc_fjord_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; omega



theorem sdc_fjord_on_41 : (![4, 1] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; left
  exact sdc_vsegUp_mem' 4 0 3 1 (by norm_num) (by norm_num)



theorem sdc_fjord_on_50 : (![5, 0] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; left
  exact sdc_hsegRight_mem' 0 4 3 5 (by norm_num) (by norm_num)



theorem sdc_fjord_on_60 : (![6, 0] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; left
  exact sdc_hsegRight_mem' 0 4 3 6 (by norm_num) (by norm_num)



theorem sdc_fjord_on_71 : (![7, 1] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; left
  exact sdc_vsegUp_mem' 7 0 4 1 (by norm_num) (by norm_num)


theorem sdc_fjord_interior_51 : (![5, 1] : Site 2) ∈ jec_leftRegion sdc_fjord := by
  rw [jec_mem_leftRegion, sdc_fjord_raycount]
  norm_num


theorem sdc_fjord_interior_11 : (![1, 1] : Site 2) ∈ jec_leftRegion sdc_fjord := by
  rw [jec_mem_leftRegion, sdc_fjord_raycount]
  norm_num


theorem sdc_fjord_mem_interior_51 : (![5, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord :=
  (jil_mem_offSupportInterior sdc_fjord _).mpr ⟨sdc_fjord_off_51, sdc_fjord_interior_51⟩


theorem sdc_fjord_mem_interior_11 : (![1, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord :=
  (jil_mem_offSupportInterior sdc_fjord _).mpr ⟨sdc_fjord_off_11, sdc_fjord_interior_11⟩












theorem sdc_fjord_body_false :
    ¬ ∃ cx : ℤ, (5 : ℤ) ≤ cx ∧
        (∀ t : ℤ, (5 : ℤ) ≤ t → t ≤ cx → (![t, 1] : Site 2) ∉ sdc_fjord.support) ∧
        (![cx, 1 - 1] : Site 2) ∉ sdc_fjord.support := by
  rintro ⟨cx, hxcx, hrun, hcdown⟩
  
  have hcx6 : cx ≤ 6 := by
    by_contra hcon
    push Not at hcon
    exact hrun 7 (by norm_num) (by omega) sdc_fjord_on_71
  
  have hcx5 : cx = 5 ∨ cx = 6 := by omega
  have : (![cx, (1 : ℤ) - 1] : Site 2) ∈ sdc_fjord.support := by
    rcases hcx5 with h | h <;> subst h
    · simpa using sdc_fjord_on_50
    · simpa using sdc_fjord_on_60
  exact hcdown this






theorem sdc_segmentDown_false :
    ∃ (seed : Site 2), seed ∈ jil_offSupportInterior sdc_fjord ∧
      ¬ rlc_SegmentDown sdc_fjord seed := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded sdc_fjord
  obtain ⟨seed, hseed, hmin⟩ :=
    rlc_exists_lexMin_seed sdc_fjord sdc_fjord_mem_interior_11 M
  refine ⟨seed, hseed, ?_⟩
  intro hres
  
  have hbox11 := hMb _ sdc_fjord_interior_11
  have hbox51 := hMb _ sdc_fjord_interior_51
  have hlt : rlc_lexMeasure M (![1, 1] : Site 2) < rlc_lexMeasure M (![5, 1] : Site 2) := by
    obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hbox11
    obtain ⟨⟨g0a, g0b⟩, ⟨g1a, g1b⟩⟩ := hbox51
    refine rlc_lexMeasure_lt (z := (![5, 1] : Site 2)) (z' := (![1, 1] : Site 2))
      (by simpa using g0a) (by simpa using g0b) (by simpa using g1a) (by simpa using g1b)
      (by simpa using h0a) (by simpa using h0b) (by simpa using h1a) (by simpa using h1b)
      (Or.inr ⟨by norm_num, by norm_num⟩)
  have hseedne : seed ≠ (![5, 1] : Site 2) := by
    intro heq
    have := hmin _ sdc_fjord_mem_interior_11
    rw [heq] at this
    omega
  
  have hleft : (![(![5, 1] : Site 2) 0 - 1, (![5, 1] : Site 2) 1] : Site 2) ∈ sdc_fjord.support := by
    simpa using sdc_fjord_on_41
  
  obtain ⟨cx, hxcx, hrun, hcdown⟩ :=
    hres (![5, 1] : Site 2) sdc_fjord_mem_interior_51 (fun h => hseedne h.symm) hleft
  refine sdc_fjord_body_false ⟨cx, by simpa using hxcx, ?_, by simpa using hcdown⟩
  intro t ht ht'
  have := hrun t (by simpa using ht) ht'
  simpa using this




theorem sdc_forall_segmentDown_false :
    ¬ ∀ seed : Site 2, rlc_SegmentDown sdc_fjord seed := by
  intro h
  obtain ⟨seed, _, hbad⟩ := sdc_segmentDown_false
  exact hbad (h seed)

end Lattice

end StatMech
