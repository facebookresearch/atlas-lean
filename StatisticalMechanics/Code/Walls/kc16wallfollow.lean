/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Code.Walls.kc9core

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}














theorem kc16_climbUp (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) (k : ℕ)
    (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0, z 1 + (k : ℤ)] := by
  induction k with
  | zero =>
    have h0 : (![z 0, z 1 + ((0 : ℕ) : ℤ)] : Site 2) = z := by ext i; fin_cases i <;> simp
    rw [h0]
  | succ n ih =>
    have hstep := ih (fun j hj => hoff j (by omega))
    have hadj : (hypercubicLattice 2).Adj (![z 0, z 1 + (n : ℤ)] : Site 2)
        ![z 0, z 1 + ((n + 1 : ℕ) : ℤ)] := by
      have h := sw_adj_vertSucc (z 0) (z 1 + (n : ℤ))
      have heq : (![z 0, z 1 + (n : ℤ) + 1] : Site 2) = ![z 0, z 1 + ((n + 1 : ℕ) : ℤ)] := by
        ext i; fin_cases i <;> simp; ring
      rwa [heq] at h
    exact hstep.trans
      (Adj.reachable ⟨hadj, hoff n (by omega), hoff (n + 1) (by omega)⟩ :
        (offSupport Vc).Reachable _ _)




theorem kc16_climbDown (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) (k : ℕ)
    (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0, z 1 - (k : ℤ)] := by
  induction k with
  | zero =>
    have h0 : (![z 0, z 1 - ((0 : ℕ) : ℤ)] : Site 2) = z := by ext i; fin_cases i <;> simp
    rw [h0]
  | succ n ih =>
    have hstep := ih (fun j hj => hoff j (by omega))
    have hadj : (hypercubicLattice 2).Adj (![z 0, z 1 - ((n + 1 : ℕ) : ℤ)] : Site 2)
        ![z 0, z 1 - (n : ℤ)] := by
      have h := sw_adj_vertSucc (z 0) (z 1 - ((n + 1 : ℕ) : ℤ))
      have heq : (![z 0, z 1 - ((n + 1 : ℕ) : ℤ) + 1] : Site 2) = ![z 0, z 1 - (n : ℤ)] := by
        ext i; fin_cases i <;> simp; ring
      rwa [heq] at h
    exact hstep.trans
      (Adj.reachable ⟨hadj.symm, hoff n (by omega), hoff (n + 1) (by omega)⟩ :
        (offSupport Vc).Reachable _ _)






theorem kc16_climbUp_step (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) (k : ℕ)
    (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support)
    (hright : (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support) :
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
  have hclimb := kc16_climbUp Vc z k hoff
  have hadj : (hypercubicLattice 2).Adj (![z 0, z 1 + (k : ℤ)] : Site 2)
      ![z 0 + 1, z 1 + (k : ℤ)] := sw_adj_horizSucc (z 1 + (k : ℤ)) (z 0)
  exact ⟨![z 0 + 1, z 1 + (k : ℤ)], by simp,
    hclimb.trans (Adj.reachable ⟨hadj, hoff k (le_refl k), hright⟩ :
      (offSupport Vc).Reachable _ _)⟩




theorem kc16_climbDown_step (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) (k : ℕ)
    (hoff : ∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support)
    (hright : (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support) :
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w := by
  have hclimb := kc16_climbDown Vc z k hoff
  have hadj : (hypercubicLattice 2).Adj (![z 0, z 1 - (k : ℤ)] : Site 2)
      ![z 0 + 1, z 1 - (k : ℤ)] := sw_adj_horizSucc (z 1 - (k : ℤ)) (z 0)
  exact ⟨![z 0 + 1, z 1 - (k : ℤ)], by simp,
    hclimb.trans (Adj.reachable ⟨hadj, hoff k (le_refl k), hright⟩ :
      (offSupport Vc).Reachable _ _)⟩












def kc16_VerticalDetour (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
    (![z 0 + 1, z 1] : Site 2) ∈ Vc.support →
    (∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) ∧
        (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support) ∨
    (∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) ∧
        (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support)





theorem kc16_rightDodge_of_verticalDetour (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hdet : kc16_VerticalDetour Vc R) : ecc_RightDodge Vc R := by
  intro z hzout hzoff hzR hnb
  rcases hdet z hzout hzoff hzR hnb with ⟨k, hoff, hright⟩ | ⟨k, hoff, hright⟩
  · exact kc16_climbUp_step Vc z k hoff hright
  · exact kc16_climbDown_step Vc z k hoff hright




theorem kc16_offSupportReaches_of_verticalDetour (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hdet : kc16_VerticalDetour Vc R) : kc5_OffSupportReachesExterior Vc R :=
  kc9_offSupportReaches_of_rightDodge Vc R (kc16_rightDodge_of_verticalDetour Vc R hdet)











theorem kc16_offSupport_of_row_high (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {w : Site 2} (hw : (R : ℤ) < w 1 ∨ w 1 < -(R : ℤ)) :
    w ∉ Vc.support := by
  intro hmem
  have hbox := hsupp ((oc_mem_supportSet Vc w).mpr hmem) 1
  have habs : |w 1| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbox
  rw [abs_le] at habs
  omega






theorem kc16_detour_up_of_homeColumnClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (z : Site 2) (hzrow : z 1 ≤ (R : ℤ))
    (hcol : ∀ j : ℕ, j ≤ ((R : ℤ) + 1 - z 1).toNat →
        (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) :
    ∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) ∧
        (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support := by
  refine ⟨((R : ℤ) + 1 - z 1).toNat, hcol, ?_⟩
  apply kc16_offSupport_of_row_high Vc R hsupp
  left
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have : (((R : ℤ) + 1 - z 1).toNat : ℤ) = (R : ℤ) + 1 - z 1 := by omega
  rw [this]; omega





theorem kc16_detour_down_of_homeColumnClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (z : Site 2) (hzrow : -(R : ℤ) ≤ z 1)
    (hcol : ∀ j : ℕ, j ≤ ((R : ℤ) + 1 + z 1).toNat →
        (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) :
    ∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) ∧
        (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support := by
  refine ⟨((R : ℤ) + 1 + z 1).toNat, hcol, ?_⟩
  apply kc16_offSupport_of_row_high Vc R hsupp
  right
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have : (((R : ℤ) + 1 + z 1).toNat : ℤ) = (R : ℤ) + 1 + z 1 := by omega
  rw [this]; omega














def kc16_ClearEscapeColumn (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
    (![z 0 + 1, z 1] : Site 2) ∈ Vc.support →
    (z 1 ≤ (R : ℤ) ∧ ∀ j : ℕ, j ≤ ((R : ℤ) + 1 - z 1).toNat →
        (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) ∨
    (-(R : ℤ) ≤ z 1 ∧ ∀ j : ℕ, j ≤ ((R : ℤ) + 1 + z 1).toNat →
        (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support)




theorem kc16_verticalDetour_of_clearEscapeColumn (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hcol : kc16_ClearEscapeColumn Vc R) : kc16_VerticalDetour Vc R := by
  intro z hzout hzoff hzR hnb
  rcases hcol z hzout hzoff hzR hnb with ⟨hrow, hup⟩ | ⟨hrow, hdown⟩
  · exact Or.inl (kc16_detour_up_of_homeColumnClear Vc R hsupp z hrow hup)
  · exact Or.inr (kc16_detour_down_of_homeColumnClear Vc R hsupp z hrow hdown)





theorem kc16_rightDodge_of_clearEscapeColumn (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hcol : kc16_ClearEscapeColumn Vc R) : ecc_RightDodge Vc R :=
  kc16_rightDodge_of_verticalDetour Vc R
    (kc16_verticalDetour_of_clearEscapeColumn Vc R hsupp hcol)




theorem kc16_offSupportReaches_of_clearEscapeColumn (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hcol : kc16_ClearEscapeColumn Vc R) : kc5_OffSupportReachesExterior Vc R :=
  kc9_offSupportReaches_of_rightDodge Vc R (kc16_rightDodge_of_clearEscapeColumn Vc R hsupp hcol)






theorem kc16_offSupportOutsideInfinite_of_clearEscapeColumn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hcol : kc16_ClearEscapeColumn (mpl_orbitLoop K a) R) :
    kc7_OffSupportOutsideInfinite K a := by
  have hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R := by
    intro z hz; exact hRbox ((oc_mem_supportSet _ z).mp hz)
  exact kc9_offSupportOutsideInfinite_of_rightDodge K a R hRbox hbridge
    (kc16_rightDodge_of_clearEscapeColumn (mpl_orbitLoop K a) R hsupp hcol)














theorem kc16_unitCell_clearEscapeColumn :
    kc16_ClearEscapeColumn (mpl_orbitLoop unitCell ucBase) 1 := by
  intro z _ hzoff _ hnb
  obtain ⟨hnb0, hnb1⟩ := kc8_unitCell_support_coords _ hnb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hnb0 hnb1
  
  have hz0 : z 0 = -2 := by
    rcases hnb0 with h | h
    · omega
    · exact absurd (kc8_unitCell_coords_in_support z (by omega) hnb1) hzoff
  
  refine Or.inl ⟨by omega, ?_⟩
  intro j _ hsupp
  obtain ⟨hc0, _⟩ := kc8_unitCell_support_coords _ hsupp
  simp only [Matrix.cons_val_zero] at hc0
  omega


theorem kc16_unitCell_verticalDetour :
    kc16_VerticalDetour (mpl_orbitLoop unitCell ucBase) 1 :=
  kc16_verticalDetour_of_clearEscapeColumn (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc16_unitCell_clearEscapeColumn





theorem kc16_unitCell_rightDodge :
    ecc_RightDodge (mpl_orbitLoop unitCell ucBase) 1 :=
  kc16_rightDodge_of_clearEscapeColumn (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc16_unitCell_clearEscapeColumn


theorem kc16_unitCell_offSupportReaches :
    kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 :=
  kc16_offSupportReaches_of_clearEscapeColumn (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc16_unitCell_clearEscapeColumn






















theorem kc16_cappedColumn_no_detour (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hnb : (![z 0 + 1, z 1] : Site 2) ∈ Vc.support)
    (hup : (![z 0, z 1 + (1 : ℤ)] : Site 2) ∈ Vc.support)
    (hdown : (![z 0, z 1 - (1 : ℤ)] : Site 2) ∈ Vc.support) :
    ¬ ((∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 + (j : ℤ)] : Site 2) ∉ Vc.support) ∧
          (![z 0 + 1, z 1 + (k : ℤ)] : Site 2) ∉ Vc.support) ∨
       (∃ k : ℕ, (∀ j : ℕ, j ≤ k → (![z 0, z 1 - (j : ℤ)] : Site 2) ∉ Vc.support) ∧
          (![z 0 + 1, z 1 - (k : ℤ)] : Site 2) ∉ Vc.support)) := by
  have hcast1 : ((1 : ℕ) : ℤ) = (1 : ℤ) := by norm_num
  rintro (⟨k, hoff, hrk⟩ | ⟨k, hoff, hrk⟩)
  · 
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have : (![z 0 + 1, z 1 + ((0 : ℕ) : ℤ)] : Site 2) = (![z 0 + 1, z 1] : Site 2) := by
        ext i; fin_cases i <;> simp
      rw [this] at hrk; exact hrk hnb
    · have h1 : (![z 0, z 1 + ((1 : ℕ) : ℤ)] : Site 2) = (![z 0, z 1 + (1 : ℤ)] : Site 2) := by
        ext i; fin_cases i <;> simp
      exact (hoff 1 hkpos) (h1 ▸ hup)
  · 
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have : (![z 0 + 1, z 1 - ((0 : ℕ) : ℤ)] : Site 2) = (![z 0 + 1, z 1] : Site 2) := by
        ext i; fin_cases i <;> simp
      rw [this] at hrk; exact hrk hnb
    · have h1 : (![z 0, z 1 - ((1 : ℕ) : ℤ)] : Site 2) = (![z 0, z 1 - (1 : ℤ)] : Site 2) := by
        ext i; fin_cases i <;> simp
      exact (hoff 1 hkpos) (h1 ▸ hdown)

end Walls

end StatMech
