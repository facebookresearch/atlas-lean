/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Sharpness.Simon
import Code.Ising.GKS
import Code.Ising.GKS2

open Finset BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]









lemma ghy_ZJ_insert_factor (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    {x y : V} (hxy : x ≠ y) (he : s(x, y) ∉ E) :
    ZJ (insert s(x, y) E) J hf
      = ZJ E J hf
        * (Real.cosh (J s(x, y)) + Real.sinh (J s(x, y)) * expJ E J hf (spinProd {x, y})) := by
  have hZ0 : 0 < ZJ E J hf := ZJ_pos E J hf
  have hZb : ZJ (insert s(x, y) E) J hf
      = Real.cosh (J s(x, y)) * ZJ E J hf
        + Real.sinh (J s(x, y)) * (∑ s, spinProd {x, y} s * wJ E J hf s) := by
    unfold ZJ
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [wJ_insert s(x, y) E he J hf s,
      exp_mul_pm (J s(x, y)) (bond s s(x, y)) (bond_eq_pm s s(x, y)),
      bond_eq_spinProd_pair s hxy]
    ring
  have hexp : (∑ s, spinProd {x, y} s * wJ E J hf s)
      = expJ E J hf (spinProd {x, y}) * ZJ E J hf := by
    unfold expJ ZJ
    rw [div_mul_cancel₀]
    exact ne_of_gt (by unfold ZJ at hZ0; exact hZ0)
  rw [hZb, hexp]; ring













lemma ghy_ratio_insert (C D : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v)
    (hCD : C ⊆ D) (hnd : ∀ e ∈ D, ¬ e.IsDiag)
    {x y : V} (hxy : x ≠ y) (heD : s(x, y) ∉ D) :
    ZJ (insert s(x, y) C) J hf * ZJ D J hf ≤ ZJ (insert s(x, y) D) J hf * ZJ C J hf := by
  have heC : s(x, y) ∉ C := fun h => heD (hCD h)
  have hfC := ghy_ZJ_insert_factor C J hf hxy heC
  have hfD := ghy_ZJ_insert_factor D J hf hxy heD
  have hMle : expJ C J hf (spinProd {x, y}) ≤ expJ D J hf (spinProd {x, y}) :=
    griffiths_mono_pair C D J hf hCD (fun e _ => hJ e) hhf (fun e he _ => hnd e he) x y
  have hsh : 0 ≤ Real.sinh (J s(x, y)) := Real.sinh_nonneg_iff.mpr (hJ s(x, y))
  have hZC := ZJ_pos C J hf
  have hZD := ZJ_pos D J hf
  rw [hfC, hfD]
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hZC.le hZD.le) hsh) (sub_nonneg.mpr hMle)]










lemma ghy_ZJ_supermod (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v)
    (C D : Finset (Sym2 V)) (hCD : C ⊆ D) (hndD : ∀ e ∈ D, ¬ e.IsDiag) :
    ∀ P : Finset (Sym2 V), Disjoint P D → (∀ e ∈ P, ¬ e.IsDiag) →
      ZJ (C ∪ P) J hf * ZJ D J hf ≤ ZJ (D ∪ P) J hf * ZJ C J hf := by
  intro P
  induction P using Finset.induction with
  | empty =>
    intro _ _
    simp only [Finset.union_empty]
    exact le_of_eq (mul_comm _ _)
  | @insert e₀ P he₀ IH =>
    intro hdisj hndP
    
    have hdisjP : Disjoint P D := hdisj.mono_left (Finset.subset_insert e₀ P)
    have hndP' : ∀ e ∈ P, ¬ e.IsDiag := fun e he => hndP e (Finset.mem_insert_of_mem he)
    have HP := IH hdisjP hndP'
    
    have he₀D : e₀ ∉ D := fun h =>
      (Finset.disjoint_left.mp hdisj (Finset.mem_insert_self e₀ P)) h
    have hnd0 : ¬ e₀.IsDiag := hndP e₀ (Finset.mem_insert_self e₀ P)
    obtain ⟨x, y, hxy, rfl⟩ := exists_pair_of_not_isDiag hnd0
    have he₀DP : s(x, y) ∉ D ∪ P := by
      rw [Finset.mem_union, not_or]; exact ⟨he₀D, he₀⟩
    have hCPDP : C ∪ P ⊆ D ∪ P := Finset.union_subset_union hCD (Finset.Subset.refl P)
    have hndDP : ∀ e ∈ D ∪ P, ¬ e.IsDiag := by
      intro e he; rw [Finset.mem_union] at he
      rcases he with h | h
      · exact hndD e h
      · exact hndP' e h
    
    have h1 := ghy_ratio_insert (C ∪ P) (D ∪ P) J hf hJ hhf hCPDP hndDP hxy he₀DP
    
    rw [Finset.union_insert, Finset.union_insert]
    have hB : 0 < ZJ (D ∪ P) J hf := ZJ_pos (D ∪ P) J hf
    have hZD : 0 ≤ ZJ D J hf := (ZJ_pos D J hf).le
    have hA₂ : 0 ≤ ZJ (insert s(x, y) (D ∪ P)) J hf := (ZJ_pos (insert s(x, y) (D ∪ P)) J hf).le
    
    nlinarith [mul_le_mul_of_nonneg_right h1 hZD, mul_le_mul_of_nonneg_left HP hA₂, hB]








lemma ghy_Zdep_supermod (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v) (hndE : ∀ e ∈ E, ¬ e.IsDiag)
    (S₁ S₂ : Finset (Sym2 V)) (hS₁ : S₁ ⊆ E) (hS₂ : S₂ ⊆ E) (hdisj : Disjoint S₁ S₂) :
    ZJ (E \ S₁) J hf * ZJ (E \ S₂) J hf ≤ ZJ E J hf * ZJ (E \ (S₁ ∪ S₂)) J hf := by
  
  have hCD : E \ (S₁ ∪ S₂) ⊆ E \ S₂ :=
    Finset.sdiff_subset_sdiff (le_refl E) (Finset.subset_union_right)
  have hndD : ∀ e ∈ E \ S₂, ¬ e.IsDiag := fun e he => hndE e (Finset.mem_sdiff.mp he).1
  have hPD : Disjoint S₂ (E \ S₂) := (Finset.sdiff_disjoint).symm
  have hndP : ∀ e ∈ S₂, ¬ e.IsDiag := fun e he => hndE e (hS₂ he)
  have key := ghy_ZJ_supermod J hf hJ hhf (E \ (S₁ ∪ S₂)) (E \ S₂) hCD hndD S₂ hPD hndP
  
  have hcup : (E \ (S₁ ∪ S₂)) ∪ S₂ = E \ S₁ := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro (⟨heE, hn⟩ | heS2)
      · exact ⟨heE, fun h => hn (Or.inl h)⟩
      · exact ⟨hS₂ heS2, fun h => Finset.disjoint_left.mp hdisj h heS2⟩
    · rintro ⟨heE, hnS1⟩
      by_cases hS2 : e ∈ S₂
      · exact Or.inr hS2
      · exact Or.inl ⟨heE, fun h => h.elim hnS1 hS2⟩
  
  have hdup : (E \ S₂) ∪ S₂ = E := Finset.sdiff_union_of_subset hS₂
  rw [hcup, hdup] at key
  exact key






noncomputable def ghy_zeta (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (S : Finset (Sym2 V)) : ℝ :=
  ZJ (E \ S) J hf / ZJ E J hf * ∏ e ∈ S, Real.cosh (J e)



noncomputable def ghy_rho (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (S : Finset (Sym2 V)) : ℝ :=
  ghy_zeta E J hf S * ∏ e ∈ S, Real.tanh (J e)


lemma ghy_zeta_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (S : Finset (Sym2 V)) : 0 ≤ ghy_zeta E J hf S := by
  unfold ghy_zeta
  apply mul_nonneg
  · exact div_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le
  · exact Finset.prod_nonneg (fun e _ => (Real.cosh_pos _).le)


lemma ghy_tanh_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr ht) (Real.cosh_pos _).le


lemma ghy_rho_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (S : Finset (Sym2 V)) : 0 ≤ ghy_rho E J hf S := by
  unfold ghy_rho
  exact mul_nonneg (ghy_zeta_nonneg E J hf S)
    (Finset.prod_nonneg (fun e _ => ghy_tanh_nonneg (hJ e)))







lemma ghy_zeta_supermult (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v) (hndE : ∀ e ∈ E, ¬ e.IsDiag)
    (S₁ S₂ : Finset (Sym2 V)) (hS₁ : S₁ ⊆ E) (hS₂ : S₂ ⊆ E) (hdisj : Disjoint S₁ S₂) :
    ghy_zeta E J hf S₁ * ghy_zeta E J hf S₂ ≤ ghy_zeta E J hf (S₁ ∪ S₂) := by
  unfold ghy_zeta
  rw [Finset.prod_union hdisj]
  set Z := ZJ E J hf with hZdef
  set a := ZJ (E \ S₁) J hf with hadef
  set b := ZJ (E \ S₂) J hf with hbdef
  set d := ZJ (E \ (S₁ ∪ S₂)) J hf with hddef
  set P₁ := ∏ e ∈ S₁, Real.cosh (J e) with hP1def
  set P₂ := ∏ e ∈ S₂, Real.cosh (J e) with hP2def
  have hZ : 0 < Z := ZJ_pos E J hf
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hP1 : 0 < P₁ := Finset.prod_pos (fun e _ => Real.cosh_pos _)
  have hP2 : 0 < P₂ := Finset.prod_pos (fun e _ => Real.cosh_pos _)
  have hdep : a * b ≤ Z * d := ghy_Zdep_supermod E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ hdisj
  
  have key : a * b / (Z * Z) ≤ d / Z := by
    rw [div_le_div_iff₀ (by positivity) hZ]
    nlinarith [hdep, hZ, mul_pos hZ hZ]
  have hL : a / Z * P₁ * (b / Z * P₂) = a * b / (Z * Z) * (P₁ * P₂) := by
    field_simp
  rw [hL]
  exact mul_le_mul_of_nonneg_right key (by positivity)




lemma ghy_rho_supermult (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v) (hndE : ∀ e ∈ E, ¬ e.IsDiag)
    (S₁ S₂ : Finset (Sym2 V)) (hS₁ : S₁ ⊆ E) (hS₂ : S₂ ⊆ E) (hdisj : Disjoint S₁ S₂) :
    ghy_rho E J hf S₁ * ghy_rho E J hf S₂ ≤ ghy_rho E J hf (S₁ ∪ S₂) := by
  unfold ghy_rho
  rw [Finset.prod_union hdisj]
  have hzeta := ghy_zeta_supermult E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ hdisj
  have hT1 : 0 ≤ ∏ e ∈ S₁, Real.tanh (J e) :=
    Finset.prod_nonneg (fun e _ => ghy_tanh_nonneg (hJ e))
  have hT2 : 0 ≤ ∏ e ∈ S₂, Real.tanh (J e) :=
    Finset.prod_nonneg (fun e _ => ghy_tanh_nonneg (hJ e))
  have hstep := mul_le_mul_of_nonneg_right hzeta (mul_nonneg hT1 hT2)
  calc ghy_zeta E J hf S₁ * (∏ e ∈ S₁, Real.tanh (J e))
          * (ghy_zeta E J hf S₂ * (∏ e ∈ S₂, Real.tanh (J e)))
      = ghy_zeta E J hf S₁ * ghy_zeta E J hf S₂
          * ((∏ e ∈ S₁, Real.tanh (J e)) * (∏ e ∈ S₂, Real.tanh (J e))) := by ring
    _ ≤ ghy_zeta E J hf (S₁ ∪ S₂)
          * ((∏ e ∈ S₁, Real.tanh (J e)) * (∏ e ∈ S₂, Real.tanh (J e))) := hstep









theorem ghy_rho_supermult_three (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v) (hndE : ∀ e ∈ E, ¬ e.IsDiag)
    (S₁ S₂ S₃ : Finset (Sym2 V)) (hS₁ : S₁ ⊆ E) (hS₂ : S₂ ⊆ E) (hS₃ : S₃ ⊆ E)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃) :
    ghy_rho E J hf S₁ * ghy_rho E J hf S₂ * ghy_rho E J hf S₃
      ≤ ghy_rho E J hf (S₁ ∪ S₂ ∪ S₃) := by
  have hStep1 := ghy_rho_supermult E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ h12
  have hUnion12 : S₁ ∪ S₂ ⊆ E := Finset.union_subset hS₁ hS₂
  have hDisj123 : Disjoint (S₁ ∪ S₂) S₃ := Finset.disjoint_union_left.mpr ⟨h13, h23⟩
  have hStep2 := ghy_rho_supermult E J hf hJ hhf hndE (S₁ ∪ S₂) S₃ hUnion12 hS₃ hDisj123
  have hρ3 : 0 ≤ ghy_rho E J hf S₃ := ghy_rho_nonneg E J hf hJ S₃
  calc ghy_rho E J hf S₁ * ghy_rho E J hf S₂ * ghy_rho E J hf S₃
      ≤ ghy_rho E J hf (S₁ ∪ S₂) * ghy_rho E J hf S₃ :=
        mul_le_mul_of_nonneg_right hStep1 hρ3
    _ ≤ ghy_rho E J hf (S₁ ∪ S₂ ∪ S₃) := hStep2

end StatMech.Walls
