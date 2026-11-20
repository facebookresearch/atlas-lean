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
import Code.Lattice.JordanInteriorLib
import Code.Lattice.InteriorWindingClose
import Code.Lattice.SegmentDownClose
import Code.Lattice.MatchedConnectivityInterior
import Code.Lattice.RowLinkedClose
import Code.Lattice.KingInteriorFloodClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice









noncomputable def ksd_stair : (hypercubicLattice 2).Walk ![(0:ℤ),(0:ℤ)] ![(0:ℤ),(0:ℤ)] :=
  let s1 : (hypercubicLattice 2).Walk ![(0:ℤ),0] ![2,0] :=
    (jec_hsegRight 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![(2:ℤ),0] ![2,1] :=
    (jec_vsegUp 2 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![(2:ℤ),1] ![3,1] :=
    (jec_hsegRight 1 2 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s4 : (hypercubicLattice 2).Walk ![(3:ℤ),1] ![3,3] :=
    (jec_vsegUp 3 1 2).copy rfl (by ext i; fin_cases i <;> simp)
  let s5 : (hypercubicLattice 2).Walk ![(3:ℤ),3] ![1,3] :=
    ((jec_hsegRight 3 1 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s6 : (hypercubicLattice 2).Walk ![(1:ℤ),3] ![1,2] :=
    ((jec_vsegUp 1 2 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s7 : (hypercubicLattice 2).Walk ![(1:ℤ),2] ![0,2] :=
    ((jec_hsegRight 2 0 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s8 : (hypercubicLattice 2).Walk ![(0:ℤ),2] ![0,0] :=
    ((jec_vsegUp 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append s8))))))




theorem ksd_stair_raycount (z : Site 2) :
    jec_rayCount z ksd_stair =
      (if 2 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (1:ℤ) - 1 then 1 else 0)
      + (if 3 ≤ z 0 - 1 ∧ 1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 1 + (2:ℤ) - 1 then 1 else 0)
      + (if 1 ≤ z 0 - 1 ∧ 2 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 2 + (1:ℤ) - 1 then 1 else 0)
      + (if 0 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (2:ℤ) - 1 then 1 else 0) := by
  unfold ksd_stair
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight]
  push_cast; ring_nf





theorem ksd_stair_support_locus (p : Site 2) (hp : p ∈ ksd_stair.support) :
      (p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ 2) ∨
      (p 0 = 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1) ∨
      (p 1 = 1 ∧ 2 ≤ p 0 ∧ p 0 ≤ 3) ∨
      (p 0 = 3 ∧ 1 ≤ p 1 ∧ p 1 ≤ 3) ∨
      (p 1 = 3 ∧ 1 ≤ p 0 ∧ p 0 ≤ 3) ∨
      (p 0 = 1 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3) ∨
      (p 1 = 2 ∧ 0 ≤ p 0 ∧ p 0 ≤ 1) ∨
      (p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2) := by
  unfold ksd_stair at hp
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
  rcases hp with h|h|h|h|h|h|h|h
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 0 0 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 2 0 1 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 1 2 1 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 3 1 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 3 1 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 1 2 1 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 2 0 1 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 0 0 2 h; push_cast at *; omega


theorem ksd_off_11 : (![1, 1] : Site 2) ∉ ksd_stair.support := by
  intro h; have := ksd_stair_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this; omega


theorem ksd_off_22 : (![2, 2] : Site 2) ∉ ksd_stair.support := by
  intro h; have := ksd_stair_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this; omega



theorem ksd_on_12 : (![1, 2] : Site 2) ∈ ksd_stair.support := by
  unfold ksd_stair
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; left
  exact sdc_vsegUp_mem' 1 2 1 2 (by norm_num) (by norm_num)



theorem ksd_on_21 : (![2, 1] : Site 2) ∈ ksd_stair.support := by
  unfold ksd_stair
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; left
  exact sdc_hsegRight_mem' 1 2 1 2 (by norm_num) (by norm_num)



theorem ksd_on_32 : (![3, 2] : Site 2) ∈ ksd_stair.support := by
  unfold ksd_stair
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; left
  exact sdc_vsegUp_mem' 3 1 2 2 (by norm_num) (by norm_num)








theorem ksd_hsegRight_edge_mem (row : ℤ) : ∀ (k j : ℕ), ∀ (t : ℤ), j < k →
    s((![t + (j:ℤ), row] : Site 2), (![t + (j:ℤ) + 1, row] : Site 2)) ∈
      (jec_hsegRight row t k).edges := by
  intro k
  induction k with
  | zero => intro j t hj; omega
  | succ k ih =>
    intro j t hj
    rw [jec_hsegRight, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [List.mem_cons]; left
      simp only [Nat.cast_zero, add_zero]
    · rw [List.mem_cons]; right
      have hh := ih (j - 1) (t + 1) (by omega)
      have heq : s((![t + (j:ℤ), row] : Site 2), (![t + (j:ℤ) + 1, row] : Site 2)) =
          s((![(t + 1) + ((j - 1 : ℕ):ℤ), row] : Site 2),
             (![(t + 1) + ((j - 1 : ℕ):ℤ) + 1, row] : Site 2)) := by
        congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
      rw [heq]; exact hh



theorem ksd_vsegUp_edge_mem (col : ℤ) : ∀ (k j : ℕ), ∀ (r : ℤ), j < k →
    s((![col, r + (j:ℤ)] : Site 2), (![col, r + (j:ℤ) + 1] : Site 2)) ∈
      (jec_vsegUp col r k).edges := by
  intro k
  induction k with
  | zero => intro j r hj; omega
  | succ k ih =>
    intro j r hj
    rw [jec_vsegUp, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [List.mem_cons]; left
      simp only [Nat.cast_zero, add_zero]
    · rw [List.mem_cons]; right
      have hh := ih (j - 1) (r + 1) (by omega)
      have heq : s((![col, r + (j:ℤ)] : Site 2), (![col, r + (j:ℤ) + 1] : Site 2)) =
          s((![col, (r + 1) + ((j - 1 : ℕ):ℤ)] : Site 2),
             (![col, (r + 1) + ((j - 1 : ℕ):ℤ) + 1] : Site 2)) := by
        congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
      rw [heq]; exact hh


theorem ksd_hsegRight_edge_mem' (row t : ℤ) (k : ℕ) (c : ℤ) (h1 : t ≤ c) (h2 : c < t + (k:ℤ)) :
    s((![c, row] : Site 2), (![c + 1, row] : Site 2)) ∈ (jec_hsegRight row t k).edges := by
  have hh := ksd_hsegRight_edge_mem row k (c - t).toNat t (by omega)
  have heq : s((![t + ((c - t).toNat : ℤ), row] : Site 2),
        (![t + ((c - t).toNat : ℤ) + 1, row] : Site 2)) =
      s((![c, row] : Site 2), (![c + 1, row] : Site 2)) := by
    congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
  rwa [heq] at hh


theorem ksd_vsegUp_edge_mem' (col r : ℤ) (k : ℕ) (c : ℤ) (h1 : r ≤ c) (h2 : c < r + (k:ℤ)) :
    s((![col, c] : Site 2), (![col, c + 1] : Site 2)) ∈ (jec_vsegUp col r k).edges := by
  have hh := ksd_vsegUp_edge_mem col k (c - r).toNat r (by omega)
  have heq : s((![col, r + ((c - r).toNat : ℤ)] : Site 2),
        (![col, r + ((c - r).toNat : ℤ) + 1] : Site 2)) =
      s((![col, c] : Site 2), (![col, c + 1] : Site 2)) := by
    congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
  rwa [heq] at hh




theorem ksd_interior_11 : (![1, 1] : Site 2) ∈ jec_leftRegion ksd_stair := by
  rw [jec_mem_leftRegion, ksd_stair_raycount]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  decide


theorem ksd_interior_22 : (![2, 2] : Site 2) ∈ jec_leftRegion ksd_stair := by
  rw [jec_mem_leftRegion, ksd_stair_raycount]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  decide


theorem ksd_mem_interior_11 : (![1, 1] : Site 2) ∈ jil_offSupportInterior ksd_stair :=
  (jil_mem_offSupportInterior ksd_stair _).mpr ⟨ksd_off_11, ksd_interior_11⟩


theorem ksd_mem_interior_22 : (![2, 2] : Site 2) ∈ jil_offSupportInterior ksd_stair :=
  (jil_mem_offSupportInterior ksd_stair _).mpr ⟨ksd_off_22, ksd_interior_22⟩


theorem ksd_on_23 : (![2, 3] : Site 2) ∈ ksd_stair.support := by
  unfold ksd_stair
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; left
  exact sdc_hsegRight_mem' 3 1 2 2 (by norm_num) (by norm_num)


theorem ksd_on_33 : (![3, 3] : Site 2) ∈ ksd_stair.support := by
  unfold ksd_stair
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; left
  exact sdc_vsegUp_mem' 3 1 2 3 (by norm_num) (by norm_num)





theorem ksd_interior_eq :
    jil_offSupportInterior ksd_stair = {(![1, 1] : Site 2), (![2, 2] : Site 2)} := by
  ext z
  rw [jil_mem_offSupportInterior, jec_mem_leftRegion, ksd_stair_raycount]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  
  have key : (z = (![1, 1] : Site 2) ↔ z 0 = 1 ∧ z 1 = 1) ∧
      (z = (![2, 2] : Site 2) ↔ z 0 = 2 ∧ z 1 = 2) := by
    refine ⟨⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩, ⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩⟩
    · rw [h]; exact ⟨by simp, by simp⟩
    · ext i; fin_cases i <;> simp [h0, h1]
    · rw [h]; exact ⟨by simp, by simp⟩
    · ext i; fin_cases i <;> simp [h0, h1]
  rw [key.1, key.2]
  
  have eq21 : z = (![2, 1] : Site 2) ↔ z 0 = 2 ∧ z 1 = 1 :=
    ⟨fun h => ⟨by rw [h]; simp, by rw [h]; simp⟩, fun ⟨h0, h1⟩ => by ext i; fin_cases i <;> simp [h0, h1]⟩
  have eq12 : z = (![1, 2] : Site 2) ↔ z 0 = 1 ∧ z 1 = 2 :=
    ⟨fun h => ⟨by rw [h]; simp, by rw [h]; simp⟩, fun ⟨h0, h1⟩ => by ext i; fin_cases i <;> simp [h0, h1]⟩
  have eq32 : z = (![3, 2] : Site 2) ↔ z 0 = 3 ∧ z 1 = 2 :=
    ⟨fun h => ⟨by rw [h]; simp, by rw [h]; simp⟩, fun ⟨h0, h1⟩ => by ext i; fin_cases i <;> simp [h0, h1]⟩
  have eq23 : z = (![2, 3] : Site 2) ↔ z 0 = 2 ∧ z 1 = 3 :=
    ⟨fun h => ⟨by rw [h]; simp, by rw [h]; simp⟩, fun ⟨h0, h1⟩ => by ext i; fin_cases i <;> simp [h0, h1]⟩
  have eq33 : z = (![3, 3] : Site 2) ↔ z 0 = 3 ∧ z 1 = 3 :=
    ⟨fun h => ⟨by rw [h]; simp, by rw [h]; simp⟩, fun ⟨h0, h1⟩ => by ext i; fin_cases i <;> simp [h0, h1]⟩
  
  have h21 : ¬ (z 0 = 2 ∧ z 1 = 1 ∧ z ∉ ksd_stair.support) := fun ⟨a, b, c⟩ =>
    c (eq21.mpr ⟨a, b⟩ ▸ ksd_on_21)
  have h12 : ¬ (z 0 = 1 ∧ z 1 = 2 ∧ z ∉ ksd_stair.support) := fun ⟨a, b, c⟩ =>
    c (eq12.mpr ⟨a, b⟩ ▸ ksd_on_12)
  have h32 : ¬ (z 0 = 3 ∧ z 1 = 2 ∧ z ∉ ksd_stair.support) := fun ⟨a, b, c⟩ =>
    c (eq32.mpr ⟨a, b⟩ ▸ ksd_on_32)
  have h23 : ¬ (z 0 = 2 ∧ z 1 = 3 ∧ z ∉ ksd_stair.support) := fun ⟨a, b, c⟩ =>
    c (eq23.mpr ⟨a, b⟩ ▸ ksd_on_23)
  have h33 : ¬ (z 0 = 3 ∧ z 1 = 3 ∧ z ∉ ksd_stair.support) := fun ⟨a, b, c⟩ =>
    c (eq33.mpr ⟨a, b⟩ ▸ ksd_on_33)
  
  set R : ℤ → ℤ → ℕ := fun a b =>
      (if 2 ≤ a - 1 ∧ 0 ≤ b - 1 ∧ b - 1 ≤ 0 + (1:ℤ) - 1 then 1 else 0)
      + (if 3 ≤ a - 1 ∧ 1 ≤ b - 1 ∧ b - 1 ≤ 1 + (2:ℤ) - 1 then 1 else 0)
      + (if 1 ≤ a - 1 ∧ 2 ≤ b - 1 ∧ b - 1 ≤ 2 + (1:ℤ) - 1 then 1 else 0)
      + (if 0 ≤ a - 1 ∧ 0 ≤ b - 1 ∧ b - 1 ≤ 0 + (2:ℤ) - 1 then 1 else 0) with hR
  
  have bounds : ∀ a b : ℤ, ¬ Even (R a b) → (1 ≤ b ∧ b ≤ 3) ∧ 1 ≤ a := by
    intro a b hodd
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    · by_contra hcon
      revert hodd
      simp only [hR]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      decide
  
  have evenBig : ∀ a b : ℤ, 1 ≤ b → b ≤ 3 → 4 ≤ a → Even (R a b) := by
    intro a b _ _ ha
    simp only [hR]
    rcases (by omega : b = 1 ∨ b = 2 ∨ b = 3) with hb | hb | hb <;> subst hb
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; decide
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]; decide
    · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)]; decide
  constructor
  · rintro ⟨hoff, hodd⟩
    have hoddR : ¬ Even (R (z 0) (z 1)) := by simpa only [hR] using hodd
    obtain ⟨⟨hb1, hb2⟩, ha1⟩ := bounds (z 0) (z 1) hoddR
    have ha2 : z 0 ≤ 3 := by
      by_contra hcon
      exact hoddR (evenBig (z 0) (z 1) hb1 hb2 (by omega))
    
    rcases (by omega : z 0 = 1 ∨ z 0 = 2 ∨ z 0 = 3) with h0 | h0 | h0 <;>
      rcases (by omega : z 1 = 1 ∨ z 1 = 2 ∨ z 1 = 3) with h1 | h1 | h1
    · exact Or.inl ⟨h0, h1⟩                          
    · exact absurd ⟨h0, h1, hoff⟩ h12                
    · exact absurd (by simp only [hR, h0, h1]; decide) hoddR  
    · exact absurd ⟨h0, h1, hoff⟩ h21                
    · exact Or.inr ⟨h0, h1⟩                          
    · exact absurd ⟨h0, h1, hoff⟩ h23                
    · exact absurd (by simp only [hR, h0, h1]; decide) hoddR  
    · exact absurd ⟨h0, h1, hoff⟩ h32                
    · exact absurd ⟨h0, h1, hoff⟩ h33                
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · refine ⟨(key.1.mpr ⟨h0, h1⟩) ▸ ksd_off_11, ?_⟩
      simp only [h0, h1]; decide
    · refine ⟨(key.2.mpr ⟨h0, h1⟩) ▸ ksd_off_22, ?_⟩
      simp only [h0, h1]; decide










theorem ksd_support_cells (p : Site 2) (hp : p ∈ ksd_stair.support) :
    p = (![0,0]:Site 2) ∨ p = (![1,0]:Site 2) ∨ p = (![2,0]:Site 2) ∨ p = (![2,1]:Site 2) ∨
    p = (![3,1]:Site 2) ∨ p = (![3,2]:Site 2) ∨ p = (![3,3]:Site 2) ∨ p = (![2,3]:Site 2) ∨
    p = (![1,3]:Site 2) ∨ p = (![1,2]:Site 2) ∨ p = (![0,2]:Site 2) ∨ p = (![0,1]:Site 2) := by
  have hl := ksd_stair_support_locus p hp
  
  have toCell : ∀ a b : ℤ, p 0 = a → p 1 = b → p = (![a, b] : Site 2) := by
    intro a b h0 h1; ext i; fin_cases i <;> simp [h0, h1]
  
  
  have hpair : (p 0 = 0 ∧ p 1 = 0) ∨ (p 0 = 1 ∧ p 1 = 0) ∨ (p 0 = 2 ∧ p 1 = 0) ∨
      (p 0 = 2 ∧ p 1 = 1) ∨ (p 0 = 3 ∧ p 1 = 1) ∨ (p 0 = 3 ∧ p 1 = 2) ∨
      (p 0 = 3 ∧ p 1 = 3) ∨ (p 0 = 2 ∧ p 1 = 3) ∨ (p 0 = 1 ∧ p 1 = 3) ∨
      (p 0 = 1 ∧ p 1 = 2) ∨ (p 0 = 0 ∧ p 1 = 2) ∨ (p 0 = 0 ∧ p 1 = 1) := by
    rcases hl with h|h|h|h|h|h|h|h <;> omega
  rcases hpair with ⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩
  · exact Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (toCell _ _ h0 h1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr (toCell _ _ h0 h1)






theorem ksd_stair_fourThin : mci_FourThin ksd_stair := by
  intro u v hu hv hadj
  
  have edges_mem : ∀ e : Sym2 (Site 2),
      (e = s((![0,0]:Site 2),(![1,0]:Site 2)) ∨ e = s((![1,0]:Site 2),(![2,0]:Site 2)) ∨
       e = s((![2,0]:Site 2),(![2,1]:Site 2)) ∨ e = s((![2,1]:Site 2),(![3,1]:Site 2)) ∨
       e = s((![3,1]:Site 2),(![3,2]:Site 2)) ∨ e = s((![3,2]:Site 2),(![3,3]:Site 2)) ∨
       e = s((![3,3]:Site 2),(![2,3]:Site 2)) ∨ e = s((![2,3]:Site 2),(![1,3]:Site 2)) ∨
       e = s((![1,3]:Site 2),(![1,2]:Site 2)) ∨ e = s((![1,2]:Site 2),(![0,2]:Site 2)) ∨
       e = s((![0,2]:Site 2),(![0,1]:Site 2)) ∨ e = s((![0,1]:Site 2),(![0,0]:Site 2))) →
      e ∈ ksd_stair.edges := by
    rintro e (h|h|h|h|h|h|h|h|h|h|h|h) <;> subst h <;> unfold ksd_stair <;>
      simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_reverse]
    · left; have := ksd_hsegRight_edge_mem' 0 0 2 0 (by norm_num) (by norm_num); simpa using this
    · left; have := ksd_hsegRight_edge_mem' 0 0 2 1 (by norm_num) (by norm_num); simpa using this
    · right; left; have := ksd_vsegUp_edge_mem' 2 0 1 0 (by norm_num) (by norm_num); simpa using this
    · right; right; left
      have := ksd_hsegRight_edge_mem' 1 2 1 2 (by norm_num) (by norm_num); simpa using this
    · right; right; right; left
      have := ksd_vsegUp_edge_mem' 3 1 2 1 (by norm_num) (by norm_num); simpa using this
    · right; right; right; left
      have := ksd_vsegUp_edge_mem' 3 1 2 2 (by norm_num) (by norm_num); simpa using this
    · right; right; right; right; left
      have := ksd_hsegRight_edge_mem' 3 1 2 2 (by norm_num) (by norm_num)
      rw [Sym2.eq_swap]; simpa using this
    · right; right; right; right; left
      have := ksd_hsegRight_edge_mem' 3 1 2 1 (by norm_num) (by norm_num)
      rw [Sym2.eq_swap]; simpa using this
    · right; right; right; right; right; left
      have := ksd_vsegUp_edge_mem' 1 2 1 2 (by norm_num) (by norm_num)
      rw [Sym2.eq_swap]; simpa using this
    · right; right; right; right; right; right; left
      have := ksd_hsegRight_edge_mem' 2 0 1 0 (by norm_num) (by norm_num)
      rw [Sym2.eq_swap]; simpa using this
    · right; right; right; right; right; right; right
      have := ksd_vsegUp_edge_mem' 0 0 2 1 (by norm_num) (by norm_num)
      rw [Sym2.eq_swap]; simpa using this
    · right; right; right; right; right; right; right
      have := ksd_vsegUp_edge_mem' 0 0 2 0 (by norm_num) (by norm_num)
      rw [Sym2.eq_swap]; simpa using this
  
  have hu12 := ksd_support_cells u hu
  have hv12 := ksd_support_cells v hv
  apply edges_mem
  
  
  rcases hu12 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hv12 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first
        | (exfalso; revert hadj; rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
        | (revert hadj; decide)












theorem ksd_seed_is_11 {M : ℤ}
    (hMb : ∀ z ∈ jec_leftRegion ksd_stair, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {seed : Site 2} (hseed : seed ∈ jil_offSupportInterior ksd_stair)
    (hmin : ∀ z ∈ jil_offSupportInterior ksd_stair,
      rlc_lexMeasure M seed ≤ rlc_lexMeasure M z) :
    seed = (![1, 1] : Site 2) := by
  
  have hmem : seed ∈ ({(![1, 1] : Site 2), (![2, 2] : Site 2)} : Set (Site 2)) := by
    rw [← ksd_interior_eq]; exact hseed
  rcases hmem with h | h
  · exact h
  · exfalso
    
    have hbox11 := hMb _ ksd_interior_11
    have hbox22 := hMb _ ksd_interior_22
    obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hbox11
    obtain ⟨⟨g0a, g0b⟩, ⟨g1a, g1b⟩⟩ := hbox22
    have hlt : rlc_lexMeasure M (![1, 1] : Site 2) < rlc_lexMeasure M (![2, 2] : Site 2) :=
      rlc_lexMeasure_lt (z := (![2, 2] : Site 2)) (z' := (![1, 1] : Site 2))
        (by simpa using g0a) (by simpa using g0b) (by simpa using g1a) (by simpa using g1b)
        (by simpa using h0a) (by simpa using h0b) (by simpa using h1a) (by simpa using h1b)
        (Or.inl (by norm_num))
    have := hmin _ ksd_mem_interior_11
    rw [h] at this
    omega






theorem ksd_stair_body_false :
    ¬ ∃ cx : ℤ, (2 : ℤ) ≤ cx ∧
        (∀ t : ℤ, (2 : ℤ) ≤ t → t ≤ cx → (![t, 2] : Site 2) ∉ ksd_stair.support) ∧
        ((![cx, 2 - 1] : Site 2) ∉ ksd_stair.support ∨
          ((![cx + 1, 2] : Site 2) ∉ ksd_stair.support ∧
            (![cx + 1, 2 - 1] : Site 2) ∉ ksd_stair.support)) := by
  rintro ⟨cx, hxcx, hrun, hdesc⟩
  
  have hcx2 : cx = 2 := by
    by_contra hcon
    exact hrun 3 (by norm_num) (by omega) ksd_on_32
  subst hcx2
  rcases hdesc with hdown | ⟨helbow, _hdiag⟩
  · 
    exact hdown (by simpa using ksd_on_21)
  · 
    exact helbow (by simpa using ksd_on_32)











theorem ksd_kingSegmentDown_false :
    ¬ kif_KingSegmentDown ksd_stair (![1, 1] : Site 2) := by
  intro hres
  
  have hne : (![2, 2] : Site 2) ≠ (![1, 1] : Site 2) := by
    intro h; have := congrFun h 0; simp at this
  have hleft : (![(![2, 2] : Site 2) 0 - 1, (![2, 2] : Site 2) 1] : Site 2) ∈ ksd_stair.support := by
    simpa using ksd_on_12
  obtain ⟨cx, hxcx, hrun, hdesc⟩ := hres (![2, 2] : Site 2) ksd_mem_interior_22 hne hleft
  refine ksd_stair_body_false ⟨cx, by simpa using hxcx, ?_, ?_⟩
  · intro t ht ht'; have := hrun t (by simpa using ht) ht'; simpa using this
  · rcases hdesc with hdown | ⟨helbow, hdiag⟩
    · exact Or.inl (by simpa using hdown)
    · exact Or.inr ⟨by simpa using helbow, by simpa using hdiag⟩





theorem ksd_kingSegmentDown_lexMinSeed_false :
    ∃ seed : Site 2, seed ∈ jil_offSupportInterior ksd_stair ∧
      ¬ kif_KingSegmentDown ksd_stair seed := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded ksd_stair
  obtain ⟨seed, hseed, hmin⟩ :=
    rlc_exists_lexMin_seed ksd_stair ksd_mem_interior_11 M
  refine ⟨seed, hseed, ?_⟩
  rw [ksd_seed_is_11 hMb hseed hmin]
  exact ksd_kingSegmentDown_false















theorem ksd_kingRowLinked : mci_KingRowLinked ksd_stair (![1, 1] : Site 2) := by
  intro z hz
  
  have hmem : z ∈ ({(![1, 1] : Site 2), (![2, 2] : Site 2)} : Set (Site 2)) := by
    rw [← ksd_interior_eq]; exact hz
  rcases hmem with h | h
  · 
    subst h
    exact ⟨SimpleGraph.Walk.nil, by
      intro w hw
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
      exact hw ▸ ksd_mem_interior_11⟩
  · 
    subst h
    have hadj : mci_kingGraph.Adj (![2, 2] : Site 2) (![1, 1] : Site 2) := by
      have h := mci_kingAdj_diag 2 2 (-1) (-1) (Or.inr rfl) (Or.inr rfl)
      simp only [show (2:ℤ) + -1 = 1 by ring] at h
      exact h
    refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact ksd_mem_interior_22
    · subst h; exact ksd_mem_interior_11








theorem ksd_residue_false_but_theorem_true :
    mci_FourThin ksd_stair ∧
    mci_KingRowLinked ksd_stair (![1, 1] : Site 2) ∧
    ¬ kif_KingSegmentDown ksd_stair (![1, 1] : Site 2) :=
  ⟨ksd_stair_fourThin, ksd_kingRowLinked, ksd_kingSegmentDown_false⟩

end Lattice

end StatMech
