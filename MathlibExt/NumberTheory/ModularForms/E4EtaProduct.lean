/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularForm_E4_mul_etaProduct_eq.lean`
and
`P2M/Sol/S_ModularForm_E4_mul_etaProduct_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Expand
public import MathlibExt.NumberTheory.ModularForms.JCoefficientBound
public import MathlibExt.NumberTheory.ModularForms.QParamProduct
public import MathlibExt.NumberTheory.ModularForms.SturmBoundGamma0

import MathlibExt.NumberTheory.ModularForms.Gamma0Index
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.NormTrace

@[expose] public section

noncomputable section

open Complex Filter Topology
open scoped MatrixGroups ModularForm Pointwise UpperHalfPlane PowerSeries.WithPiTopology

namespace ModularForm
private def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] private theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] :=
      rfl

private def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

private def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp)

@[simp] private theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (j : ℝ); 0, (p :
      ℝ)] := by
  simp [heckeMatrix, hp]

@[simp] private theorem val_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
  simp [heckeDiagMatrix, hp]

@[simp] private theorem heckeMatrix_zero (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]

@[simp] private theorem heckeDiagMatrix_zero : heckeDiagMatrix 0 = 1 := by simp [heckeDiagMatrix]

private theorem det_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) : ((heckeMatrix p j).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeMatrix hp, Matrix.det_fin_two_of]
  ring

private theorem det_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) : ((heckeDiagMatrix p).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeDiagMatrix hp, Matrix.det_fin_two_of]
  ring

private theorem det_heckeMatrix_pos (p j : ℕ) : 0 < ((heckeMatrix p j).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

private theorem det_heckeDiagMatrix_pos (p : ℕ) : 0 < ((heckeDiagMatrix p).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeDiagMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

private theorem denom_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeMatrix hp]

private theorem denom_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeDiagMatrix p) τ = 1 := by
  simp [UpperHalfPlane.denom, val_heckeDiagMatrix hp]

private theorem coe_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeMatrix hp]

private theorem coe_heckeDiagMatrix_smul {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    ((heckeDiagMatrix p • τ : UpperHalfPlane) : ℂ) = (p : ℂ) * (τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeDiagMatrix_pos p)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeDiagMatrix hp]

private theorem σ_heckeMatrix (p j : ℕ) : UpperHalfPlane.σ (heckeMatrix p j) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_heckeMatrix_pos p j)]

private theorem σ_heckeDiagMatrix (p : ℕ) : UpperHalfPlane.σ (heckeDiagMatrix p) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_heckeDiagMatrix_pos p)]

private theorem slash_heckeMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : UpperHalfPlane →
  ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeMatrix, det_heckeMatrix hp, denom_heckeMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

private theorem slash_heckeDiagMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeDiagMatrix p) τ = (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [ModularForm.slash_apply, σ_heckeDiagMatrix, det_heckeDiagMatrix hp, denom_heckeDiagMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast, one_zpow, mul_one]
  rw [mul_comm]

namespace DegeneracyPort
variable {k : ℤ}

private def restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (F : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := F
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn F γ (h hγ)
  holo' := F.holo'
  bdd_at_cusps' hc := F.bdd_at_cusps' (hc.mono h)

private def restrictCF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (F : CuspForm Γ k) :
    CuspForm Γ' k where
  toFun := F
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn F γ (h hγ)
  holo' := F.holo'
  zero_at_cusps' hc := F.zero_at_cusps' (hc.mono h)

@[scoped simp] private theorem coe_restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (F :
  ModularForm Γ k) :
    ⇑(restrictMF h F) = ⇑F := rfl

@[scoped simp] private theorem coe_restrictCF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (F :
  CuspForm Γ k) :
    ⇑(restrictCF h F) = ⇑F := rfl

private theorem Gamma0_le_conj_Gamma0 {M N d : ℕ} (hd : d ≠ 0) (hdiv : d * M ∣ N) :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (heckeDiagMatrix d)⁻¹ •
        ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨A, hA, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]

  have hN : (N : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (CongruenceSubgroup.Gamma0_mem.mp hA)
  obtain ⟨c', hc'⟩ : (d : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (Int.natCast_dvd_natCast.mpr (Dvd.intro _ rfl : d ∣ d * M)).trans
      ((Int.natCast_dvd_natCast.mpr hdiv).trans hN)
  have hMc' : (M : ℤ) ∣ c' := by
    have h1 : (d : ℤ) * M ∣ (d : ℤ) * c' := by
      rw [← hc']; exact_mod_cast (Int.natCast_dvd_natCast.mpr hdiv).trans hN
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hd)).mp h1
  have hdet : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [← Matrix.det_fin_two, A.det_coe]

  let B : SL(2, ℤ) := ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, d * (A : Matrix (Fin 2) (Fin 2) ℤ) 0
    1;
      c', (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc'⟩
  refine ⟨B, ?_, ?_⟩
  · rw [SetLike.mem_coe, CongruenceSubgroup.Gamma0_mem]
    show ((c' : ℤ) : ZMod M) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hMc'
  · have hc'' : ((A.1 1 0 : ℤ) : ℝ) = (d : ℝ) * (c' : ℝ) := by exact_mod_cast hc'
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix, val_heckeDiagMatrix hd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, B, Matrix.SpecialLinearGroup.map_apply_coe,
        Matrix.map_apply, hc'', mul_comm]
    · left; rfl
    · show ((d * A.1 0 1 : ℤ) : ℝ) = (d : ℝ) * ((A.1 0 1 : ℤ) : ℝ); norm_cast
    · rw [show ((c' : ℝ) * (d : ℝ)) = (d : ℝ) * (c' : ℝ) from mul_comm _ _,
        mul_right_inj' (show (d : ℝ) ≠ 0 by exact_mod_cast hd)]
      rfl
    · rfl

private theorem exists_modularForm {M N d : ℕ} [NeZero N] (hdiv : d * M ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) := by
  have hd : d ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hdiv
    exact NeZero.ne N hdiv
  have hdk : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hd)
  refine ⟨((d : ℂ) ^ (k - 1))⁻¹ •
    restrictMF (Gamma0_le_conj_Gamma0 hd hdiv) (ModularForm.translate f (heckeDiagMatrix d)), ?_⟩
  funext τ
  rw [ModularForm.IsGLPos.coe_smul, Pi.smul_apply, coe_restrictMF, ModularForm.coe_translate,
    slash_heckeDiagMatrix_apply k hd, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdk, one_mul]

private theorem exists_cuspForm {M N d : ℕ} [NeZero N] (hdiv : d * M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k,
      ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) := by
  have hd : d ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hdiv
    exact NeZero.ne N hdiv
  have hdk : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hd)
  refine ⟨((d : ℂ) ^ (k - 1))⁻¹ •
    restrictCF (Gamma0_le_conj_Gamma0 hd hdiv) (CuspForm.translate f (heckeDiagMatrix d)), ?_⟩
  funext τ
  rw [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, coe_restrictCF]
  show ((d : ℂ) ^ (k - 1))⁻¹ • (⇑f ∣[k] heckeDiagMatrix d) τ = _
  rw [slash_heckeDiagMatrix_apply k hd, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdk, one_mul]

end DegeneracyPort
end ModularForm

namespace ModularCurve

namespace EtaQSeries

open Filter Topology Polynomial
open scoped PowerSeries.WithPiTopology

private def f (N : ℕ) : PowerSeries ℤ := ∏ n ∈ Finset.range N, ((1 : PowerSeries ℤ) - PowerSeries.X
  ^ (n + 1))

private def Cong (m : ℕ) (G : PowerSeries ℤ) : Prop := (PowerSeries.X : PowerSeries ℤ) ^ (m + 1) ∣
  G - 1

private theorem Cong.mul {m : ℕ} {G H : PowerSeries ℤ} (hG : Cong m G) (hH : Cong m H) : Cong m (G
  * H) := by
  have : G * H - 1 = (G - 1) * H + (H - 1) := by ring
  rw [Cong, this]
  exact dvd_add (hG.mul_right _) hH

private theorem Cong.one (m : ℕ) : Cong m 1 := by simp [Cong]

private theorem Cong.pow {m : ℕ} {G : PowerSeries ℤ} (hG : Cong m G) (a : ℕ) : Cong m (G ^ a) := by
  induction a with
  | zero => simpa using Cong.one m
  | succ a ih => rw [pow_succ]; exact ih.mul hG

private theorem Cong.prod {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → PowerSeries ℤ} (hg : ∀ i ∈ s,
  Cong m (g i)) :
    Cong m (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong.one m
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hg i (Finset.mem_insert_self i s)).mul (ih fun j hj => hg j (Finset.mem_insert_of_mem
      hj))

private theorem Cong.one_sub_X_pow {m n : ℕ} (hn : m + 1 ≤ n + 1) : Cong m (1 - PowerSeries.X ^ (n
  + 1)) := by
  rw [Cong, sub_sub_cancel_left, dvd_neg]
  exact pow_dvd_pow _ hn

private theorem coeff_mul_of_cong {m : ℕ} {G : PowerSeries ℤ} (hG : Cong m G) (H : PowerSeries ℤ) :
    PowerSeries.coeff m (H * G) = PowerSeries.coeff m H := by
  obtain ⟨K, hK⟩ := hG
  have : G = 1 + PowerSeries.X ^ (m + 1) * K := by rw [← hK]; ring
  rw [this, mul_add, mul_one, map_add, ← mul_assoc, mul_comm H, mul_assoc,
    PowerSeries.coeff_X_pow_mul',
    if_neg (by omega), add_zero]

private theorem coeff_prod_pow_eq (a m : ℕ) (s : Finset ℕ) (hs : Finset.range (m + 1) ⊆ s) :
    PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a) =
      PowerSeries.coeff m (f (m + 1) ^ a) := by
  rw [← Finset.prod_sdiff hs, mul_pow, mul_comm, f]
  apply coeff_mul_of_cong
  apply Cong.pow
  apply Cong.prod
  intro n hn
  rw [Finset.mem_sdiff, Finset.mem_range, not_lt] at hn
  exact Cong.one_sub_X_pow (by omega)

private theorem coeff_etaProd_pow (a m : ℕ) :
    PowerSeries.coeff m (etaProd ^ a) = PowerSeries.coeff m (f (m + 1) ^ a) := by
  have hmult := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have h1 : Tendsto (fun s : Finset ℕ => ∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1)))
    atTop
      (𝓝 etaProd) := hmult.hasProd
  have h2 : Tendsto (fun s : Finset ℕ =>
      PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a)) atTop
      (𝓝 (PowerSeries.coeff m (etaProd ^ a))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ m).tendsto _).comp (h1.pow a)
  have h3 : Tendsto (fun s : Finset ℕ =>
      PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a)) atTop
      (𝓝 (PowerSeries.coeff m (f (m + 1) ^ a))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Finset.range (m + 1))] with s hs
    exact (coeff_prod_pow_eq a m s hs).symm
  exact tendsto_nhds_unique h2 h3

private theorem coeff_etaProd_pow_eq_coeff_f (a m N : ℕ) (hN : m < N) :
    PowerSeries.coeff m (etaProd ^ a) = PowerSeries.coeff m (f N ^ a) := by
  rw [coeff_etaProd_pow]
  exact (coeff_prod_pow_eq a m (Finset.range N) (Finset.range_subset_range.mpr hN)).symm

private def p (N : ℕ) : Polynomial ℤ := ∏ n ∈ Finset.range N, ((1 : Polynomial ℤ) - Polynomial.X ^
  (n + 1))

private theorem coe_p (N : ℕ) : ((p N : Polynomial ℤ) : PowerSeries ℤ) = f N := by
  rw [p, f, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl (fun n _ => ?_)
  rw [map_sub, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

private theorem coeff_f_pow (a N m : ℕ) : PowerSeries.coeff m (f N ^ a) = (p N ^ a).coeff m := by
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow, coe_p]

private theorem eval₂_p_pow (a N : ℕ) (q : ℂ) :
    (p N ^ a).eval₂ (Int.castRingHom ℂ) q = (∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a := by
  rw [Polynomial.eval₂_pow, p, Polynomial.eval₂_finsetProd]
  simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow]

private theorem hasSum_partial (a N : ℕ) (q : ℂ) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (f N ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a) := by
  rw [← eval₂_p_pow, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp_rw [coeff_f_pow]
  apply hasSum_sum_of_ne_finset_zero
  intro m hm
  rw [Polynomial.notMem_support_iff.mp hm, Int.cast_zero, zero_mul]

private def Maj (φ : Polynomial ℤ) (Φ : Polynomial ℝ) : Prop := ∀ m, |((φ.coeff m : ℤ) : ℝ)| ≤
  Φ.coeff m

private theorem Maj.nonneg {φ : Polynomial ℤ} {Φ : Polynomial ℝ} (h : Maj φ Φ) (m : ℕ) : 0 ≤
  Φ.coeff m :=
  (abs_nonneg _).trans (h m)

private theorem Maj.mul {φ ψ : Polynomial ℤ} {Φ Ψ : Polynomial ℝ} (hφ : Maj φ Φ) (hψ : Maj ψ Ψ) :
  Maj (φ * ψ) (Φ * Ψ) := by
  intro m
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul, Int.cast_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [Int.cast_mul, abs_mul]
  exact mul_le_mul (hφ _) (hψ _) (abs_nonneg _) (hφ.nonneg _)

private theorem Maj.one : Maj 1 1 := by
  intro m
  rw [Polynomial.coeff_one, Polynomial.coeff_one]
  split_ifs <;> simp

private theorem Maj.pow {φ : Polynomial ℤ} {Φ : Polynomial ℝ} (h : Maj φ Φ) (a : ℕ) : Maj (φ ^ a)
  (Φ ^ a) := by
  induction a with
  | zero => simpa using Maj.one
  | succ a ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem Maj.prod {ι : Type*} (s : Finset ι) {φ : ι → Polynomial ℤ} {Φ : ι → Polynomial ℝ}
    (h : ∀ i ∈ s, Maj (φ i) (Φ i)) : Maj (∏ i ∈ s, φ i) (∏ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Maj.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem Maj.one_sub_X_pow (k : ℕ) : Maj (1 - Polynomial.X ^ k) (1 + Polynomial.X ^ k) := by
  intro m
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X_pow, Int.cast_sub]
  refine (abs_sub _ _).trans ?_
  split_ifs <;> simp

private def P (N : ℕ) : Polynomial ℝ := ∏ n ∈ Finset.range N, ((1 : Polynomial ℝ) + Polynomial.X ^
  (n + 1))

private theorem maj_p_pow (a N : ℕ) : Maj (p N ^ a) (P N ^ a) :=
  (Maj.prod (Finset.range N) fun n _ => Maj.one_sub_X_pow (n + 1)).pow a

private theorem eval_P_pow (a N : ℕ) (r : ℝ) : (P N ^ a).eval r = (∏ n ∈ Finset.range N, (1 + r ^
  (n + 1))) ^ a := by
  rw [Polynomial.eval_pow, P, Polynomial.eval_prod]
  simp

private theorem coeff_mul_pow_le_eval {Φ : Polynomial ℝ} (hΦ : ∀ m, 0 ≤ Φ.coeff m) {r : ℝ} (hr : 0
  ≤ r) (m : ℕ) :
    Φ.coeff m * r ^ m ≤ Φ.eval r := by
  rw [Polynomial.eval_eq_sum_range' (n := max (Φ.natDegree + 1) (m + 1)) (lt_max_of_lt_left
    (Nat.lt_succ_self _))]
  refine Finset.single_le_sum (f := fun i => Φ.coeff i * r ^ i) (fun i _ => mul_nonneg (hΦ i)
    (pow_nonneg hr i))
    (Finset.mem_range.mpr (lt_max_of_lt_right (Nat.lt_succ_self m)))

private theorem prod_one_add_le_exp {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∏ n ∈ Finset.range N, (1 + r ^ (n + 1)) ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) := by
  have hsum : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
  calc ∏ n ∈ Finset.range N, (1 + r ^ (n + 1)) ≤ ∏ n ∈ Finset.range N, Real.exp (r ^ (n + 1)) :=
        Finset.prod_le_prod₀ (fun n _ => by positivity) (fun n _ => by
          have := Real.add_one_le_exp (r ^ (n + 1)); linarith)
    _ = Real.exp (∑ n ∈ Finset.range N, r ^ (n + 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) :=
        Real.exp_le_exp.mpr (hsum.sum_le_tsum _ (fun n _ => pow_nonneg hr0 _))

private theorem norm_coeff_f_pow_mul_le (a N m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a := by
  have hmaj := maj_p_pow a N
  calc |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m ≤ (P N ^ a).coeff m * r ^ m := by
        rw [coeff_f_pow]; exact mul_le_mul_of_nonneg_right (hmaj m) (pow_nonneg hr0 m)
    _ ≤ (P N ^ a).eval r := coeff_mul_pow_le_eval hmaj.nonneg hr0 m
    _ = (∏ n ∈ Finset.range N, (1 + r ^ (n + 1))) ^ a := eval_P_pow a N r
    _ ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a :=
        pow_le_pow_left₀ (Finset.prod_nonneg fun n _ => by positivity) (prod_one_add_le_exp hr0
          hr1) a

private theorem main (a : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a) := by

  set r : ℝ := (‖q‖ + 1) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hqr : ‖q‖ < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg q) hqr
  set ρ : ℝ := ‖q‖ / r with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (norm_nonneg q) hr0
  have hρ1 : ρ < 1 := (div_lt_one hrpos).mpr hqr
  set C : ℝ := Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a with hC

  let F : ℕ → ℕ → ℂ := fun N m => ((PowerSeries.coeff m (f N ^ a) : ℤ) : ℂ) * q ^ m
  let g : ℕ → ℂ := fun m => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m
  have hbound : ∀ N m, ‖F N m‖ ≤ C * ρ ^ m := by
    intro N m
    have h1 := norm_coeff_f_pow_mul_le a N m hr0 hr1
    have hqm : ‖q‖ ^ m = r ^ m * ρ ^ m := by
      rw [← mul_pow, hρ, mul_div_cancel₀ _ hrpos.ne']
    calc ‖F N m‖ = |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * ‖q‖ ^ m := by
          simp only [F, norm_mul, norm_pow, Complex.norm_intCast]
      _ = |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m * ρ ^ m := by rw [hqm, mul_assoc]
      _ ≤ C * ρ ^ m := mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ0 m)
  have hsumm : Summable (fun m : ℕ => C * ρ ^ m) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left C
  have hlim : ∀ m, Tendsto (fun N => F N m) atTop (𝓝 (g m)) := by
    intro m
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop m] with N hN
    simp only [F, g, coeff_etaProd_pow_eq_coeff_f a m N hN]

  have hT : Tendsto (fun N => ∑' m, F N m) atTop (𝓝 (∑' m, g m)) :=
    tendsto_tsum_of_dominated_convergence hsumm hlim (Eventually.of_forall hbound)

  have hP : ∀ N, ∑' m, F N m = (∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a :=
    fun N => (hasSum_partial a N q).tsum_eq
  have hA : Tendsto (fun N => ∑' m, F N m) atTop (𝓝 ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a)) := by
    simp_rw [hP]
    exact ((ModularForm.multipliable_one_sub_pow hq).hasProd.tendsto_prod_nat).pow a
  have heq : ∑' m, g m = (∏' n : ℕ, (1 - q ^ (n + 1))) ^ a := tendsto_nhds_unique hT hA

  have hg : Summable g := by
    refine Summable.of_norm_bounded hsumm (fun m => ?_)
    have := hbound (m + 1) m
    simpa only [F, g, coeff_etaProd_pow_eq_coeff_f a m (m + 1) (Nat.lt_succ_self m)] using this
  rw [← heq]
  exact hg.hasSum

end EtaQSeries
private theorem hasSum_coeff_etaProd_pow (a : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a) :=
  EtaQSeries.main a hq
private theorem qExpansion_E4_eq_map_eisenstein4 : UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ =
  PowerSeries.map (Int.castRingHom ℂ) ModularCurve.eisenstein4 := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩ m, PowerSeries.coeff_map, eisenstein4,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four,
      ArithmeticFunction.sigma_apply]
    simp only [eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
      Int.cast_natCast]
    push_cast
    ring
private theorem hasSum_coeff_eisenstein4_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m eisenstein4 : ℤ) : ℂ) * Function.Periodic.qParam 1
      (τ : ℂ) ^ m)
      (ModularForm.E₄ τ) := by
  have h := UpperHalfPlane.hasSum_qExpansion (f := ⇑ModularForm.E₄) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularFormClass.holo ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄) τ
  rw [ModularCurve.qExpansion_E4_eq_map_eisenstein4] at h
  simpa only [PowerSeries.coeff_map, smul_eq_mul, eq_intCast] using h
private theorem gamma0_one_eq_top_aux : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private lemma coe_Gamma0_one_eq_SL :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [gamma0_one_eq_top_aux]
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

private def transportCuspForm {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ₁ = Γ₂) (f : CuspForm
  Γ₁ k) :
    CuspForm Γ₂ k := h ▸ f

@[scoped simp] private lemma transportCuspForm_coe {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h :
  Γ₁ = Γ₂)
    (f : CuspForm Γ₁ k) : ⇑(transportCuspForm h f) = ⇑f := by subst h; rfl

private def deltaGamma0 : CuspForm (CongruenceSubgroup.Gamma0 1) 12 :=
  transportCuspForm coe_Gamma0_one_eq_SL.symm CuspForm.discriminant

@[scoped simp] private lemma deltaGamma0_coe : ⇑deltaGamma0 = ModularForm.discriminant := by
  simp [deltaGamma0]

private theorem exists_gamma0_apply_eq_eta_mul_pow_twentyfour (N : ℕ) [NeZero N] :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 12,
      ∀ τ : UpperHalfPlane, g τ = ModularForm.eta (N * (τ : ℂ)) ^ 24 := by
  obtain ⟨g, hg⟩ := ModularForm.DegeneracyPort.exists_cuspForm (N := N) (d := N) (M := 1)
    (dvd_of_eq (mul_one N)) deltaGamma0
  refine ⟨g, fun τ => ?_⟩
  rw [hg]
  simp only [deltaGamma0_coe, ModularForm.discriminant]
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne N)]
end ModularCurve

private theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

private theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]


private theorem exists_gamma0_qExpansion_eq_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm
  𝒮ℒ k) :
    ∃ G : ModularForm (CongruenceSubgroup.Gamma0 N) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  obtain ⟨G, hG⟩ := ModularForm.DegeneracyPort.exists_modularForm (show 1 * 1 ∣ N by simp)
    (ModularForm.mcast rfl F gamma0_one_coe)
  refine ⟨G, ?_⟩
  rw [hG, heckeDiagMatrix_one]
  funext τ
  rw [one_smul]
  rfl

noncomputable section

namespace EtaGamma0Four
open ModularGroup Complex
open ModularForm (eta eta_q eta_q_eq_cexp)
open scoped Real

private def Fc (a b c : ℕ) (w : ℂ) : ℂ := η w ^ a * η (2 * w) ^ b * η (4 * w) ^ c

private def F (a b c : ℕ) (z : ℍ) : ℂ := Fc a b c z

private def Gc (a b c : ℕ) (w : ℂ) : ℂ := η w ^ a * η (w / 2) ^ b * η (w / 4) ^ c

private lemma eta_q_add_int (n : ℕ) (w : ℂ) (m : ℤ) : eta_q n (w + m) = eta_q n w := by
  rw [eta_q_eq_cexp, eta_q_eq_cexp]
  have : 2 * ↑π * I * (↑n + 1) * (w + ↑m) =
      2 * ↑π * I * (↑n + 1) * w + ((((n : ℤ) + 1) * m : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma eta_add_int (w : ℂ) (m : ℤ) : η (w + m) = cexp (π * I * m / 12) * η w := by
  unfold ModularForm.eta
  simp_rw [eta_q_add_int]
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← mul_assoc]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma eta_add_int_pow (w : ℂ) (m : ℤ) (e : ℕ) : η (w + m) ^ e = cexp (π * I * (m * e) / 12)
  * η w ^ e := by
  rw [eta_add_int, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  ring

private lemma cexp_phase_eq_one (s : ℤ) (h : (24 : ℤ) ∣ s) : cexp (π * I * s / 12) = 1 := by
  obtain ⟨t, rfl⟩ := h
  have : (π * I * ((24 * t : ℤ) : ℂ) / 12) = t * (2 * π * I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

private lemma Fc_add_int (a b c : ℕ) (w : ℂ) (m : ℤ) :
    Fc a b c (w + m) = cexp (π * I * ((m * (a + 2 * b + 4 * c : ℕ) : ℤ) : ℂ) / 12) * Fc a b c w :=
      by
  unfold Fc
  have h2 : 2 * (w + m) = 2 * w + ((2 * m : ℤ) : ℂ) := by push_cast; ring
  have h4 : 4 * (w + m) = 4 * w + ((4 * m : ℤ) : ℂ) := by push_cast; ring
  rw [h2, h4, eta_add_int_pow, eta_add_int_pow, eta_add_int_pow]
  have : cexp (π * I * (m * a) / 12) * η w ^ a * (cexp (π * I * (((2 * m : ℤ) : ℂ) * b) / 12) * η
    (2 * w) ^ b) *
      (cexp (π * I * (((4 * m : ℤ) : ℂ) * c) / 12) * η (4 * w) ^ c) =
      (cexp (π * I * (m * a) / 12) * cexp (π * I * (((2 * m : ℤ) : ℂ) * b) / 12) *
        cexp (π * I * (((4 * m : ℤ) : ℂ) * c) / 12)) * (η w ^ a * η (2 * w) ^ b * η (4 * w) ^ c) :=
          by ring
  rw [this, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma Gc_add_four_mul_int (a b c : ℕ) (w : ℂ) (m : ℤ) :
    Gc a b c (w + ((4 * m : ℤ) : ℂ)) = cexp (π * I * ((m * (4 * a + 2 * b + c : ℕ) : ℤ) : ℂ) / 12)
      * Gc a b c w := by
  unfold Gc
  have h2 : (w + ((4 * m : ℤ) : ℂ)) / 2 = w / 2 + ((2 * m : ℤ) : ℂ) := by push_cast; ring
  have h4 : (w + ((4 * m : ℤ) : ℂ)) / 4 = w / 4 + ((m : ℤ) : ℂ) := by push_cast; ring
  rw [h2, h4, eta_add_int_pow, eta_add_int_pow, eta_add_int_pow]
  have : cexp (π * I * (((4 * m : ℤ) : ℂ) * a) / 12) * η w ^ a * (cexp (π * I * (((2 * m : ℤ) : ℂ)
    * b) / 12) * η (w / 2) ^ b) *
      (cexp (π * I * ((m : ℂ) * c) / 12) * η (w / 4) ^ c) =
      (cexp (π * I * (((4 * m : ℤ) : ℂ) * a) / 12) * cexp (π * I * (((2 * m : ℤ) : ℂ) * b) / 12) *
        cexp (π * I * ((m : ℂ) * c) / 12)) * (η w ^ a * η (w / 2) ^ b * η (w / 4) ^ c) := by ring
  rw [this, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma Fc_add_one (a b c : ℕ) (h₁ : 24 ∣ a + 2 * b + 4 * c) (w : ℂ) : Fc a b c (w + 1) = Fc
  a b c w := by
  have := Fc_add_int a b c w 1
  rw [Int.cast_one] at this
  rw [this, cexp_phase_eq_one _ (by rw [one_mul]; exact Int.natCast_dvd_natCast.mpr h₁), one_mul]

private lemma Gc_sub_four (a b c : ℕ) (h₂ : 24 ∣ 4 * a + 2 * b + c) (w : ℂ) :
    Gc a b c (w + ((-4 : ℤ) : ℂ)) = Gc a b c w := by
  have := Gc_add_four_mul_int a b c w (-1)
  rw [show ((4 * (-1 : ℤ) : ℤ)) = -4 by norm_num] at this
  rw [this, cexp_phase_eq_one _ ?_, one_mul]
  rw [neg_mul, one_mul, dvd_neg]
  exact Int.natCast_dvd_natCast.mpr h₂

private lemma sqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  have h := Complex.cpow_nat_inv_pow w two_ne_zero
  have h2 : ((2 : ℕ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by norm_num
  rw [h2] at h
  exact h

private lemma eta_neg_inv (w : ℂ) (hw : 0 < w.im) : η (-w⁻¹) = (Complex.sqrt I)⁻¹ * (Complex.sqrt w
  * η w) := by
  have := ModularForm.eta_comp_eq_csqrt_I_inv hw
  rw [show -w⁻¹ = -1 / w by rw [neg_div, one_div]]
  simpa only [Function.comp, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using this

private lemma eta_neg_inv_pow (w : ℂ) (hw : 0 < w.im) (e : ℕ) :
    η (-w⁻¹) ^ (2 * e) = (I⁻¹ * w) ^ e * η w ^ (2 * e) := by
  rw [eta_neg_inv w hw]
  have : ((Complex.sqrt I)⁻¹ * (Complex.sqrt w * η w)) ^ (2 * e) =
      ((Complex.sqrt I ^ 2)⁻¹ * (Complex.sqrt w ^ 2)) ^ e * (η w ^ 2) ^ e := by ring
  rw [this, sqrt_sq, sqrt_sq, ← pow_mul]

private def CS (a' b' c' : ℕ) : ℂ := (I⁻¹) ^ (a' + b' + c') * (2⁻¹ : ℂ) ^ b' * (4⁻¹ : ℂ) ^ c'

private lemma CS_ne_zero (a' b' c' : ℕ) : CS a' b' c' ≠ 0 := by
  unfold CS
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero I_ne_zero)) (pow_ne_zero _ (by
    norm_num)))
    (pow_ne_zero _ (by norm_num))

private lemma Fc_neg_inv (a' b' c' : ℕ) (z : ℂ) (hz : 0 < z.im) :
    Fc (2 * a') (2 * b') (2 * c') (-z⁻¹) =
      CS a' b' c' * z ^ (a' + b' + c') * Gc (2 * a') (2 * b') (2 * c') z := by
  unfold Fc Gc CS
  have h2 : 2 * -z⁻¹ = -(z / 2)⁻¹ := by rw [inv_div]; ring
  have h4 : 4 * -z⁻¹ = -(z / 4)⁻¹ := by rw [inv_div]; ring
  have hz2 : 0 < (z / 2).im := by rw [Complex.div_ofNat_im]; positivity
  have hz4 : 0 < (z / 4).im := by rw [Complex.div_ofNat_im]; positivity
  rw [h2, h4, eta_neg_inv_pow z hz, eta_neg_inv_pow _ hz2, eta_neg_inv_pow _ hz4]
  ring

private lemma coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -((z : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]; simp [inv_neg]

private lemma denom_SL (γ : SL(2, ℤ)) (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) γ)) (z : ℂ) =
      (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := by
  simp [UpperHalfPlane.denom]

private lemma denom_S (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) ModularGroup.S)) (z : ℂ) = z := by
  rw [denom_SL]; simp [ModularGroup.coe_S]

private lemma denom_T_zpow (n : ℤ) (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) (ModularGroup.T ^ n))) (z : ℂ) = 1 := by
  rw [denom_SL]; simp [ModularGroup.coe_T_zpow]

private lemma coe_T_zpow_smul (n : ℤ) (z : ℍ) : ((ModularGroup.T ^ n • z : ℍ) : ℂ) = (z : ℂ) + n :=
  by
  rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]; push_cast; ring

private lemma F_slash_S (a' b' c' : ℕ) :
    (F (2 * a') (2 * b') (2 * c')) ∣[((a' + b' + c' : ℕ) : ℤ)] ModularGroup.S =
      fun z : ℍ => CS a' b' c' * Gc (2 * a') (2 * b') (2 * c') z := by
  ext z
  rw [ModularForm.SL_slash_apply, denom_S, F, coe_S_smul, Fc_neg_inv _ _ _ _ z.im_pos, zpow_neg,
    zpow_natCast]
  have hz : (z : ℂ) ^ (a' + b' + c') ≠ 0 := pow_ne_zero _ z.ne_zero
  field_simp

private lemma F_slash_S_slash_T (a' b' c' : ℕ) (h₂ : 24 ∣ 4 * (2 * a') + 2 * (2 * b') + 2 * c') :
    ((F (2 * a') (2 * b') (2 * c')) ∣[((a' + b' + c' : ℕ) : ℤ)] ModularGroup.S) ∣[((a' + b' + c' :
      ℕ) : ℤ)]
      (ModularGroup.T ^ (-4 : ℤ)) =
      (F (2 * a') (2 * b') (2 * c')) ∣[((a' + b' + c' : ℕ) : ℤ)] ModularGroup.S := by
  rw [F_slash_S]
  ext z
  rw [ModularForm.SL_slash_apply, denom_T_zpow, one_zpow, mul_one, coe_T_zpow_smul]
  rw [Gc_sub_four _ _ _ h₂]

end EtaGamma0Four

section gen
open Matrix.SpecialLinearGroup ModularGroup

namespace EtaGamma0Four
open ModularGroup Complex
open ModularForm (eta eta_q eta_q_eq_cexp)
open scoped Real

private def R : SL(2, ℤ) := ⟨!![1, 0; 4, 1], by norm_num [Matrix.det_fin_two_of]⟩

@[scoped simp] private lemma coe_R : (R : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 4, 1] := rfl

private def H : Subgroup SL(2, ℤ) := Subgroup.closure {ModularGroup.T, R, -1}

private lemma T_mem : ModularGroup.T ∈ H := Subgroup.subset_closure (by simp)
private lemma R_mem : R ∈ H := Subgroup.subset_closure (by simp)
private lemma neg_one_mem : (-1 : SL(2, ℤ)) ∈ H := Subgroup.subset_closure (by simp)

private lemma coe_R_zpow (n : ℤ) : ((R ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 4 *
  n, 1] := by
  induction n using Int.induction_on with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, ih, coe_R]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  | pred n ih =>
    rw [zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.SpecialLinearGroup.coe_inv,
      coe_R]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of] <;> ring

private lemma mul_T_zpow_apply (A : SL(2, ℤ)) (n : ℤ) :
    (A * ModularGroup.T ^ n) 1 0 = A 1 0 ∧ (A * ModularGroup.T ^ n) 1 1 = A 1 0 * n + A 1 1 ∧
    (A * ModularGroup.T ^ n) 0 0 = A 0 0 ∧ (A * ModularGroup.T ^ n) 0 1 = A 0 0 * n + A 0 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · show ((A : Matrix (Fin 2) (Fin 2) ℤ) * ((ModularGroup.T ^ n : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2)
    ℤ)) _ _ = _
    rw [ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma mul_R_zpow_apply (A : SL(2, ℤ)) (n : ℤ) :
    (A * R ^ n) 1 0 = A 1 0 + A 1 1 * (4 * n) ∧ (A * R ^ n) 1 1 = A 1 1 ∧
    (A * R ^ n) 0 0 = A 0 0 + A 0 1 * (4 * n) ∧ (A * R ^ n) 0 1 = A 0 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · show ((A : Matrix (Fin 2) (Fin 2) ℤ) * ((R ^ n : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) _ _ = _
    rw [coe_R_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma det_eq (A : SL(2, ℤ)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have := A.det_coe
  rw [Matrix.det_fin_two] at this
  exact this

private lemma mem_H_of_apply_one_zero_eq_zero (A : SL(2, ℤ)) (h : A 1 0 = 0) : A ∈ H := by
  have hdet := det_eq A
  rw [h, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h00 | h00
  · have h11 : A 1 1 = 1 := by rw [h00, one_mul] at hdet; exact hdet
    have : A = ModularGroup.T ^ (A 0 1) := by
      ext i j
      rw [ModularGroup.coe_T_zpow]
      fin_cases i <;> fin_cases j <;> simp [h, h00, h11]
    rw [this]
    exact Subgroup.zpow_mem _ T_mem _
  · have h11 : A 1 1 = -1 := by rw [h00] at hdet; linarith
    have : A = -1 * ModularGroup.T ^ (-(A 0 1)) := by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
      fin_cases i <;> fin_cases j <;> simp [h, h00, h11]
    rw [this]
    exact Subgroup.mul_mem _ neg_one_mem (Subgroup.zpow_mem _ T_mem _)

private lemma mem_H_of_four_dvd : ∀ (n : ℕ) (A : SL(2, ℤ)), (A 1 0).natAbs = n → (4 : ℤ) ∣ A 1 0 →
  A ∈ H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn h4
  by_cases hc : A 1 0 = 0
  · exact mem_H_of_apply_one_zero_eq_zero A hc

  set c := A 1 0 with hc_def
  set d := A 1 1 with hd_def
  have hdet := det_eq A

  have hd2 : ¬ (2 : ℤ) ∣ d := by
    intro hd
    have : (2 : ℤ) ∣ A 0 0 * A 1 1 - A 0 1 * A 1 0 :=
      dvd_sub (dvd_mul_of_dvd_right hd _) (dvd_mul_of_dvd_right ((by norm_num : (2:ℤ) ∣ 4).trans
        h4) _)
    rw [hdet] at this
    norm_num at this

  have hm0 : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hmc : ((c.natAbs : ℕ) : ℤ) = |c| := Int.natCast_natAbs c
  set d₁ : ℤ := Int.bmod d c.natAbs with hd₁
  have hd₁_eq : d₁ = d - (c.natAbs : ℤ) * Int.bdiv d c.natAbs := by
    have := Int.bdiv_add_bmod d c.natAbs
    rw [hd₁]; linarith
  have hd₁_lb : -(((c.natAbs : ℕ) : ℤ) / 2) ≤ d₁ := Int.le_bmod hm0
  have hd₁_ub : d₁ < (((c.natAbs : ℕ) : ℤ) + 1) / 2 := Int.bmod_lt hm0

  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℤ, c * n₁ = -((c.natAbs : ℤ) * Int.bdiv d c.natAbs) := by
    rw [hmc]
    rcases abs_cases c with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    exacts [⟨-(Int.bdiv d c.natAbs), by ring⟩, ⟨Int.bdiv d c.natAbs, by ring⟩]
  set A₁ := A * ModularGroup.T ^ n₁ with hA₁
  obtain ⟨hA₁c, hA₁d, -, -⟩ := mul_T_zpow_apply A n₁
  have hA₁d' : A₁ 1 1 = d₁ := by rw [hA₁d, hd₁_eq, ← hc_def, ← hd_def, hn₁]; ring

  have hm4 : (4 : ℤ) ∣ ((c.natAbs : ℕ) : ℤ) := Int.dvd_natAbs.mpr h4
  have hd₁2 : ¬ (2 : ℤ) ∣ d₁ := by
    intro h2
    apply hd2
    have : (2 : ℤ) ∣ ((c.natAbs : ℕ) : ℤ) * Int.bdiv d c.natAbs :=
      dvd_mul_of_dvd_left ((by norm_num : (2:ℤ) ∣ 4).trans hm4) _
    have := dvd_add h2 this
    rwa [hd₁_eq, sub_add_cancel] at this
  have hd₁0 : d₁ ≠ 0 := by rintro h0; exact hd₁2 (h0 ▸ dvd_zero 2)

  have hm'0 : 0 < (4 * d₁).natAbs := Int.natAbs_pos.mpr (by positivity)
  have hmm' : (((4 * d₁).natAbs : ℕ) : ℤ) = 4 * |d₁| := by
    rw [Int.natCast_natAbs, abs_mul]
    norm_num
  set c' : ℤ := Int.bmod c (4 * d₁).natAbs with hc'
  have hc'_eq : c' = c - (((4 * d₁).natAbs : ℕ) : ℤ) * Int.bdiv c (4 * d₁).natAbs := by
    have := Int.bdiv_add_bmod c (4 * d₁).natAbs
    rw [hc']; linarith
  have hc'_lb : -((((4 * d₁).natAbs : ℕ) : ℤ) / 2) ≤ c' := Int.le_bmod hm'0
  have hc'_ub : c' < ((((4 * d₁).natAbs : ℕ) : ℤ) + 1) / 2 := Int.bmod_lt hm'0
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℤ, d₁ * (4 * n₂) = -((((4 * d₁).natAbs : ℕ) : ℤ) * Int.bdiv c (4 *
    d₁).natAbs) := by
    rw [hmm']
    rcases abs_cases d₁ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    exacts [⟨-(Int.bdiv c (4 * d₁).natAbs), by ring⟩, ⟨Int.bdiv c (4 * d₁).natAbs, by ring⟩]
  set A₂ := A₁ * R ^ n₂ with hA₂
  obtain ⟨hA₂c, hA₂d, -, -⟩ := mul_R_zpow_apply A₁ n₂
  have hA₂c' : A₂ 1 0 = c' := by rw [hA₂c, hA₁c, hA₁d', ← hc_def, hn₂, hc'_eq]; ring

  have h4c' : (4 : ℤ) ∣ c' := by
    rw [hc'_eq]
    exact dvd_sub h4 (dvd_mul_of_dvd_left (Int.dvd_natAbs.mpr (dvd_mul_right 4 d₁)) _)
  have hd₁odd : d₁ % 2 = 1 := Int.two_dvd_ne_zero.mp hd₁2
  have hlt : c'.natAbs < n := by
    rw [← hn]
    zify
    rw [hmc] at hm4 hd₁_lb hd₁_ub
    rw [hmm'] at hc'_lb hc'_ub
    rcases abs_cases c with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rcases abs_cases d₁ with ⟨habs₁, _⟩ | ⟨habs₁,
      _⟩ <;>
      rcases abs_cases c' with ⟨habs', _⟩ | ⟨habs', _⟩ <;> omega

  have hA₂H : A₂ ∈ H := ih _ hlt A₂ (by rw [hA₂c']) (by rw [hA₂c']; exact h4c')
  have : A = A₂ * R ^ (-n₂) * ModularGroup.T ^ (-n₁) := by
    rw [hA₂, hA₁]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hA₂H (Subgroup.zpow_mem _ R_mem _))
    (Subgroup.zpow_mem _ T_mem _)

private theorem Gamma0_four_le_H : CongruenceSubgroup.Gamma0 4 ≤ H := by
  intro A hA
  have h4 : (4 : ℤ) ∣ A 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (CongruenceSubgroup.Gamma0_mem.mp hA)
  exact mem_H_of_four_dvd _ A rfl h4

end EtaGamma0Four

end gen

namespace EtaGamma0Four
open ModularGroup Complex
open ModularForm (eta eta_q eta_q_eq_cexp)
open scoped Real

open scoped MatrixGroups ModularForm Real UpperHalfPlane
open ModularGroup Complex
open ModularForm (eta)

private lemma coe_T_smul (z : ℍ) : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring

private lemma denom_T (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) ModularGroup.T)) (z : ℂ) = 1 := by
  rw [denom_SL]; simp [ModularGroup.coe_T]

private lemma F_slash_T (a b c : ℕ) (k : ℤ) (h₁ : 24 ∣ a + 2 * b + 4 * c) :
    (F a b c) ∣[k] ModularGroup.T = F a b c := by
  ext z
  rw [ModularForm.SL_slash_apply, denom_T, one_zpow, mul_one, F, F, coe_T_smul, Fc_add_one _ _ _ h₁]

private lemma F_slash_neg_one (a b c : ℕ) (k : ℤ) (hk : Even k) :
    (F a b c) ∣[k] (-1 : SL(2, ℤ)) = F a b c := by
  ext z
  rw [ModularForm.SL_slash_apply, denom_SL]
  have h1 : ((-1 : SL(2, ℤ)) • z) = z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.specialLinearGroup_apply]
    simp [Matrix.SpecialLinearGroup.coe_neg]
    try ring
  have h10 : ((-1 : SL(2, ℤ)) 1 0 : ℤ) = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_neg]
  have h11 : ((-1 : SL(2, ℤ)) 1 1 : ℤ) = -1 := by
    simp [Matrix.SpecialLinearGroup.coe_neg]
  rw [h1, h10, h11]
  push_cast
  rw [zero_mul, zero_add, (Even.neg hk).neg_one_zpow, mul_one]

private lemma F_slash_R (a' b' c' : ℕ) (h₂ : 24 ∣ 4 * (2 * a') + 2 * (2 * b') + 2 * c') :
    (F (2 * a') (2 * b') (2 * c')) ∣[((a' + b' + c' : ℕ) : ℤ)] R = F (2 * a') (2 * b') (2 * c') :=
      by
  have hR : R = ModularGroup.S * ModularGroup.T ^ (-4 : ℤ) * ModularGroup.S⁻¹ := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_T_zpow, ModularGroup.coe_S, coe_R]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.adjugate_fin_two_of]
  rw [hR, SlashAction.slash_mul, SlashAction.slash_mul, F_slash_S_slash_T _ _ _ h₂, ←
    SlashAction.slash_mul,
    mul_inv_cancel, SlashAction.slash_one]

private def genGL : Set (GL (Fin 2) ℝ) := (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin
  2) ℝ) '' {ModularGroup.T, R, -1}

private lemma map_H : H.map (Matrix.SpecialLinearGroup.mapGL ℝ) = Subgroup.closure genGL := by
  rw [H, MonoidHom.map_closure]; rfl

private lemma slash_eq_of_generators {f : ℍ → ℂ} {k : ℤ} (hT : f ∣[k] ModularGroup.T = f) (hR : f
  ∣[k] R = f)
    (hN : f ∣[k] (-1 : SL(2, ℤ)) = f) :
    ∀ γ ∈ ((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ =
      f := by
  have hgen : ∀ γ ∈ Subgroup.closure genGL, f ∣[k] γ = f := by
    rw [SlashInvariantForm.slash_action_generators (rfl : Subgroup.closure genGL = Subgroup.closure
      genGL)]
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hT
    · exact hR
    · exact hN
  rintro _ ⟨A, hA, rfl⟩
  apply hgen
  rw [← map_H]
  exact Subgroup.mem_map_of_mem _ (Gamma0_four_le_H hA)

private lemma F_mdifferentiable (a b c : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (F a b c) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hFc : DifferentiableOn ℂ (Fc a b c) {z : ℂ | 0 < z.im} := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hz' : 0 < z.im := hz
    have h2 : 0 < (2 * z).im := by simp [Complex.mul_im]; positivity
    have h4 : 0 < (4 * z).im := by simp [Complex.mul_im]; positivity
    unfold Fc
    refine ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz').pow _ |>.mul
      (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet h2).comp z
        (differentiableAt_id.const_mul _)).pow _)).mul
      (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet h4).comp z
        (differentiableAt_id.const_mul _)).pow _)
  refine hFc.congr fun z hz => ?_
  have hz' : 0 < z.im := hz
  simp [F, Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz']

end EtaGamma0Four

namespace EtaGamma0Four
open ModularGroup Complex
open ModularForm (eta eta_q eta_q_eq_cexp)
open scoped Real

open scoped MatrixGroups ModularForm Real UpperHalfPlane
open Complex
open ModularForm (eta)

private lemma Gamma0_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma0 M ≤
  CongruenceSubgroup.Gamma0 N := by
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact (Int.natCast_dvd_natCast.mpr h).trans hA

private lemma GammaGL_le {N M : ℕ} (h : N ∣ M) :
    ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma0_le h)

private lemma isBoundedAtImInfty_pow {f : ℍ → ℂ} (hf : UpperHalfPlane.IsBoundedAtImInfty f) :
    ∀ n : ℕ, UpperHalfPlane.IsBoundedAtImInfty (f ^ n)
  | 0 => by rw [pow_zero]; exact Filter.const_boundedAtFilter _ _
  | n + 1 => by rw [pow_succ]; exact Filter.BoundedAtFilter.mul (isBoundedAtImInfty_pow hf n) hf

private lemma isZeroAtImInfty_pow {f : ℍ → ℂ} (hf : UpperHalfPlane.IsZeroAtImInfty f) {n : ℕ} (hn :
  0 < n) :
    UpperHalfPlane.IsZeroAtImInfty (f ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [pow_succ]
  exact Filter.BoundedAtFilter.mul_zeroAtFilter
    (isBoundedAtImInfty_pow (Filter.ZeroAtFilter.boundedAtFilter hf) _) hf

private lemma isZeroAtImInfty_of_pow {f : ℍ → ℂ} {n : ℕ} (hn : 0 < n)
    (h : UpperHalfPlane.IsZeroAtImInfty (f ^ n)) : UpperHalfPlane.IsZeroAtImInfty f := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at h ⊢
  intro ε hε
  obtain ⟨A, hA⟩ := h (ε ^ n) (pow_pos hε n)
  refine ⟨A, fun z hz => ?_⟩
  have := hA z hz
  rw [Pi.pow_apply, norm_pow] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le hn.ne').mp this

private lemma isZeroAtImInfty_triple {f₁ f₂ f₄ : ℍ → ℂ} (h₁ : UpperHalfPlane.IsZeroAtImInfty f₁)
    (h₂ : UpperHalfPlane.IsZeroAtImInfty f₂) (h₄ : UpperHalfPlane.IsZeroAtImInfty f₄)
    {α β γ : ℕ} (hE : 0 < α + β + γ) :
    UpperHalfPlane.IsZeroAtImInfty (f₁ ^ α * f₂ ^ β * f₄ ^ γ) := by
  have b₁ := isBoundedAtImInfty_pow (Filter.ZeroAtFilter.boundedAtFilter h₁) α
  have b₂ := isBoundedAtImInfty_pow (Filter.ZeroAtFilter.boundedAtFilter h₂) β
  have b₄ := isBoundedAtImInfty_pow (Filter.ZeroAtFilter.boundedAtFilter h₄) γ
  rcases Nat.eq_zero_or_pos α with hα | hα
  · rcases Nat.eq_zero_or_pos β with hβ | hβ
    · have hγ : 0 < γ := by omega
      exact Filter.BoundedAtFilter.mul_zeroAtFilter (Filter.BoundedAtFilter.mul b₁ b₂)
        (isZeroAtImInfty_pow h₄ hγ)
    · exact Filter.ZeroAtFilter.mul_boundedAtFilter
        (Filter.BoundedAtFilter.mul_zeroAtFilter b₁ (isZeroAtImInfty_pow h₂ hβ)) b₄
  · exact Filter.ZeroAtFilter.mul_boundedAtFilter
      (Filter.ZeroAtFilter.mul_boundedAtFilter (isZeroAtImInfty_pow h₁ hα) b₂) b₄

private lemma F_isZeroAt (α β γ : ℕ) (hE : 0 < α + β + γ)
    (g₁ : CuspForm (CongruenceSubgroup.Gamma0 1) 12) (hg₁ : ∀ τ : ℍ, g₁ τ = η (1 * (τ : ℂ)) ^ 24)
    (g₂ : CuspForm (CongruenceSubgroup.Gamma0 2) 12) (hg₂ : ∀ τ : ℍ, g₂ τ = η (2 * (τ : ℂ)) ^ 24)
    (g₄ : CuspForm (CongruenceSubgroup.Gamma0 4) 12) (hg₄ : ∀ τ : ℍ, g₄ τ = η (4 * (τ : ℂ)) ^ 24)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    c.IsZeroAt (F (4 * α) (4 * β) (4 * γ)) ((2 * (α + β + γ) : ℕ) : ℤ) := by
  intro g hg
  have hz₁ : UpperHalfPlane.IsZeroAtImInfty ((⇑g₁) ∣[(12 : ℤ)] g) := by
    have := g₁.zero_at_cusps' (hc.mono (GammaGL_le (one_dvd 4))) g hg
    simpa using this
  have hz₂ : UpperHalfPlane.IsZeroAtImInfty ((⇑g₂) ∣[(12 : ℤ)] g) := by
    have := g₂.zero_at_cusps' (hc.mono (GammaGL_le (by norm_num : 2 ∣ 4))) g hg
    simpa using this
  have hz₄ : UpperHalfPlane.IsZeroAtImInfty ((⇑g₄) ∣[(12 : ℤ)] g) := by
    have := g₄.zero_at_cusps' hc g hg
    simpa using this
  set E := α + β + γ with hEdef
  set Dt : ℂ := ((|((Matrix.GeneralLinearGroup.det g : ℝˣ) : ℝ)| : ℝ) : ℂ) with hDt
  have hD : Dt ≠ 0 := by
    rw [hDt]; exact_mod_cast abs_ne_zero.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  have key : ∀ τ : ℍ, ((F (4 * α) (4 * β) (4 * γ)) ∣[((2 * E : ℕ) : ℤ)] g) τ ^ 6 * Dt ^ 6 =
      (((⇑g₁) ∣[(12 : ℤ)] g) τ) ^ α * (((⇑g₂) ∣[(12 : ℤ)] g) τ) ^ β * (((⇑g₄) ∣[(12 : ℤ)] g) τ) ^ γ
        * Dt ^ E := by
    intro τ
    simp only [ModularForm.slash_def]
    rw [hg₁, hg₂, hg₄]
    have hd : UpperHalfPlane.denom g τ ≠ 0 := UpperHalfPlane.denom_ne_zero g τ
    have hF : UpperHalfPlane.σ g (F (4 * α) (4 * β) (4 * γ) (g • τ)) ^ 6 =
        UpperHalfPlane.σ g (η (1 * ((g • τ : ℍ) : ℂ)) ^ 24) ^ α * UpperHalfPlane.σ g (η (2 * ((g •
          τ : ℍ) : ℂ)) ^ 24) ^ β *
          UpperHalfPlane.σ g (η (4 * ((g • τ : ℍ) : ℂ)) ^ 24) ^ γ := by
      rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
      congr 1
      simp only [F, Fc, one_mul]
      ring

    rw [show ((2 * E : ℕ) : ℤ) - 1 = ((2 * E : ℕ) : ℤ) + (-1) by ring, zpow_add₀ hD, zpow_natCast,
      zpow_neg_one,
      zpow_neg, zpow_natCast, show (12 : ℤ) - 1 = 11 by norm_num, zpow_ofNat, zpow_neg, zpow_ofNat]
    rw [← hDt]
    set d := UpperHalfPlane.denom g τ
    set X := UpperHalfPlane.σ g (F (4 * α) (4 * β) (4 * γ) (g • τ))
    set s₁ := UpperHalfPlane.σ g (η (1 * ((g • τ : ℍ) : ℂ)) ^ 24)
    set s₂ := UpperHalfPlane.σ g (η (2 * ((g • τ : ℍ) : ℂ)) ^ 24)
    set s₄ := UpperHalfPlane.σ g (η (4 * ((g • τ : ℍ) : ℂ)) ^ 24)
    have hX : (X * (Dt ^ (2 * E) * Dt⁻¹) * (d ^ (2 * E))⁻¹) ^ 6 * Dt ^ 6 = X ^ 6 * Dt ^ (12 * E) *
      (d ^ (12 * E))⁻¹ := by
      field_simp
      ring
    rw [hX, hF, hEdef]
    simp only [← inv_pow]
    ring
  have h6 : UpperHalfPlane.IsZeroAtImInfty (((F (4 * α) (4 * β) (4 * γ)) ∣[((2 * E : ℕ) : ℤ)] g) ^
    6) := by
    have hfun : ((F (4 * α) (4 * β) (4 * γ)) ∣[((2 * E : ℕ) : ℤ)] g) ^ 6 = fun τ =>
        ((((⇑g₁) ∣[(12 : ℤ)] g) ^ α * ((⇑g₂) ∣[(12 : ℤ)] g) ^ β * ((⇑g₄) ∣[(12 : ℤ)] g) ^ γ) τ) *
          (Dt ^ E * (Dt ^ 6)⁻¹) := by
      funext τ
      have := key τ
      simp only [Pi.pow_apply, Pi.mul_apply]
      field_simp
      linear_combination this
    rw [hfun]
    have := (isZeroAtImInfty_triple hz₁ hz₂ hz₄ hE).mul_const (Dt ^ E * (Dt ^ 6)⁻¹)
    simp at this
    exact this
  exact isZeroAtImInfty_of_pow (by norm_num) h6

end EtaGamma0Four

open scoped MatrixGroups in
open EtaGamma0Four in
private theorem exists_gamma0_four_apply_eq_eta_pow_mul (a b c : ℕ) (h0 : 0 < a + b + c)
    (h₁ : 24 ∣ a + 2 * b + 4 * c) (h₂ : 24 ∣ 4 * a + 2 * b + c) (hb : Even b) (h4 : 4 ∣ a + b + c) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 4) (((a + b + c) / 2 : ℕ) : ℤ),
      ∀ z : UpperHalfPlane, f z = ModularForm.eta (z : ℂ) ^ a * ModularForm.eta (2 * (z : ℂ)) ^ b *
        ModularForm.eta (4 * (z : ℂ)) ^ c := by

  have hb' : b % 2 = 0 := Nat.even_iff.mp hb
  obtain ⟨α, rfl⟩ : 4 ∣ a := by omega
  obtain ⟨β, rfl⟩ : 4 ∣ b := by omega
  obtain ⟨γ, rfl⟩ : 4 ∣ c := by omega
  have hE : 0 < α + β + γ := by omega
  have hk : (4 * α + 4 * β + 4 * γ) / 2 = 2 * α + 2 * β + 2 * γ := by omega
  rw [hk]
  have e1 : 4 * α = 2 * (2 * α) := by ring
  have e2 : 4 * β = 2 * (2 * β) := by ring
  have e3 : 4 * γ = 2 * (2 * γ) := by ring

  obtain ⟨g₁, hg₁⟩ := ModularCurve.exists_gamma0_apply_eq_eta_mul_pow_twentyfour 1
  obtain ⟨g₂, hg₂⟩ := ModularCurve.exists_gamma0_apply_eq_eta_mul_pow_twentyfour 2
  obtain ⟨g₄, hg₄⟩ := ModularCurve.exists_gamma0_apply_eq_eta_mul_pow_twentyfour 4
  push_cast at hg₁ hg₂ hg₄
  have hslash : ∀ γ' ∈ ((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2)
    ℝ)),
      (F (2 * (2 * α)) (2 * (2 * β)) (2 * (2 * γ))) ∣[((2 * α + 2 * β + 2 * γ : ℕ) : ℤ)] γ' =
        F (2 * (2 * α)) (2 * (2 * β)) (2 * (2 * γ)) := by
    refine slash_eq_of_generators (F_slash_T _ _ _ _ (by omega)) (F_slash_R _ _ _ (by omega))
      (F_slash_neg_one _ _ _ _ ?_)
    exact ⟨α + β + γ, by push_cast; ring⟩
  refine ⟨{ toFun := F (2 * (2 * α)) (2 * (2 * β)) (2 * (2 * γ))
            slash_action_eq' := hslash
            holo' := F_mdifferentiable _ _ _
            zero_at_cusps' := ?_ }, fun z => ?_⟩
  · intro c hc
    have := F_isZeroAt α β γ hE g₁ (by simpa using hg₁) g₂ hg₂ g₄ hg₄ hc
    rw [← e1, ← e2, ← e3]
    convert this using 2
    ring
  · show F (2 * (2 * α)) (2 * (2 * β)) (2 * (2 * γ)) z = _
    rw [← e1, ← e2, ← e3]
    rfl

end

namespace ModularCurve
namespace ARails

open Complex
open scoped MatrixGroups
local notation "𝕢" => Function.Periodic.qParam

private theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]
  simp

private theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2)
      ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

private theorem index_Gamma0_four : (CongruenceSubgroup.Gamma0 4).index = 6 := by
  rw [ModularCurve.Gamma0_index, show (4 : ℕ) = 2 ^ 2 by norm_num,
    ArithmeticFunction.dedekindPsi_prime_pow (p := 2) (k := 2) Nat.prime_two (by norm_num)]
  norm_num

private def toMF {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq f
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := ModularFormClass.bdd_at_cusps f

@[scoped simp] private theorem toMF_apply {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
  (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (z : UpperHalfPlane) : toMF f z = f z := rfl

private theorem qParam_two_mul (z : ℂ) : 𝕢 1 (2 * z) = 𝕢 1 z ^ 2 := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring
private theorem qParam_four_mul (z : ℂ) : 𝕢 1 (4 * z) = 𝕢 1 z ^ 4 := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring

private theorem qParam24_prefactor (z : ℂ) (a b c e : ℕ) (he : a + 2 * b + 4 * c = 24 * e) :
    𝕢 24 z ^ a * 𝕢 24 (2 * z) ^ b * 𝕢 24 (4 * z) ^ c = 𝕢 1 z ^ e := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]
  congr 1
  have h : (a : ℂ) + 2 * b + 4 * c = 24 * e := by exact_mod_cast he
  push_cast
  linear_combination (2 * Real.pi * I * z / 24) * h

private def QS (A : PowerSeries ℂ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m A * 𝕢 1 (τ : ℂ) ^ m) (F τ)

private theorem QS.mul {A B : PowerSeries ℂ} {F G : UpperHalfPlane → ℂ} (hA : QS A F) (hB : QS B G)
  :
    QS (A * B) (fun τ => F τ * G τ) := fun τ =>
  ModularCurve.hasSum_qParam_mul 1 one_pos A B F G hA hB τ

private theorem QS_X_pow (e : ℕ) : QS (PowerSeries.X ^ e) (fun τ => 𝕢 1 (τ : ℂ) ^ e) := fun τ => by
  have := hasSum_single (f := fun m : ℕ => PowerSeries.coeff m ((PowerSeries.X : PowerSeries ℂ) ^
    e) *
    𝕢 1 (τ : ℂ) ^ m) e (fun m hm => by simp [PowerSeries.coeff_X_pow, hm])
  simpa [PowerSeries.coeff_X_pow] using this

private theorem hasSum_coeff_expand (k : ℕ) (hk : k ≠ 0) (G : PowerSeries ℤ) {q g : ℂ}
    (h : HasSum (fun m : ℕ => ((PowerSeries.coeff m G : ℤ) : ℂ) * (q ^ k) ^ m) g) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.expand k hk (G.map (Int.castRingHom ℂ)))
      * q ^ n) g := by
  let i : ℕ → ℕ := fun m => k * m
  have hi : Function.Injective i := fun a b hab => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero
    hk) hab
  have hoff : ∀ n ∉ Set.range i,
      PowerSeries.coeff n (PowerSeries.expand k hk (G.map (Int.castRingHom ℂ))) * q ^ n = 0 := by
    intro n hn
    rw [PowerSeries.coeff_expand, if_neg, zero_mul]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩
  refine (hi.hasSum_iff hoff).mp ?_
  convert h using 1
  funext m
  simp only [Function.comp_apply, i]
  rw [PowerSeries.coeff_expand, if_pos (dvd_mul_right k m), Nat.mul_div_cancel_left m
    (Nat.pos_of_ne_zero hk),
    PowerSeries.coeff_map, pow_mul]
  rfl

private theorem QS_etaProd_pow (a : ℕ) :
    QS ((etaProd ^ a).map (Int.castRingHom ℂ)) (fun τ => (∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^
      a) :=
  fun τ => by
  have h := hasSum_coeff_etaProd_pow a (q := 𝕢 1 (τ : ℂ)) (by
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ)
  convert h using 2 with m <;> simp [← map_pow, PowerSeries.coeff_map]

private theorem QS_expand_etaProd_pow (k : ℕ) (hk : k ≠ 0) (a : ℕ) :
    QS (PowerSeries.expand k hk ((etaProd ^ a).map (Int.castRingHom ℂ)))
      (fun τ => (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ k) ^ (n + 1))) ^ a) := fun τ => by
  have hq : ‖𝕢 1 (τ : ℂ) ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ) hk
  exact hasSum_coeff_expand k hk (etaProd ^ a) (hasSum_coeff_etaProd_pow a hq)

private def S (a b c e : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ e * (etaProd ^ a * PowerSeries.expand 2 two_ne_zero (etaProd ^ b) *
    PowerSeries.expand 4 (by norm_num) (etaProd ^ c))

private theorem S_map (a b c e : ℕ) : (S a b c e).map (Int.castRingHom ℂ) =
    PowerSeries.X ^ e * ((etaProd ^ a).map (Int.castRingHom ℂ) *
      PowerSeries.expand 2 two_ne_zero ((etaProd ^ b).map (Int.castRingHom ℂ)) *
      PowerSeries.expand 4 (by norm_num) ((etaProd ^ c).map (Int.castRingHom ℂ))) := by
  simp only [S, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand]

private theorem eta_eq (z : ℂ) : ModularForm.eta z = 𝕢 24 z * ∏' n : ℕ, (1 - 𝕢 1 z ^ (n + 1)) := rfl

private theorem hasSum_etaProduct (a b c e : ℕ) (he : a + 2 * b + 4 * c = 24 * e) (z :
  UpperHalfPlane) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (S a b c e) : ℤ) : ℂ) * 𝕢 1 (z : ℂ) ^ m)
      (ModularForm.eta (z : ℂ) ^ a * ModularForm.eta (2 * (z : ℂ)) ^ b * ModularForm.eta (4 * (z :
        ℂ)) ^ c) := by
  have hQ := ((QS_X_pow e).mul (((QS_etaProd_pow a).mul (QS_expand_etaProd_pow 2 two_ne_zero b)).mul
    (QS_expand_etaProd_pow 4 (by norm_num) c))) z
  rw [← S_map] at hQ
  simp only [PowerSeries.coeff_map, eq_intCast] at hQ
  convert hQ using 1
  simp only [eta_eq, mul_pow, qParam_two_mul, qParam_four_mul]
  rw [← qParam24_prefactor (z : ℂ) a b c e he]
  ring

private theorem qExpansion_coeff_eq {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 4) k) (a b
  c e : ℕ)
    (he : a + 2 * b + 4 * c = 24 * e)
    (hf : ∀ z : UpperHalfPlane, f z = ModularForm.eta (z : ℂ) ^ a * ModularForm.eta (2 * (z : ℂ)) ^
      b *
      ModularForm.eta (4 * (z : ℂ)) ^ c) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 f).coeff m = ((PowerSeries.coeff m (S a b c e) : ℤ) : ℂ) := by
  symm
  refine ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma0 4) (f := f)
    (c := fun m => ((PowerSeries.coeff m (S a b c e) : ℤ) : ℂ)) (fun τ => ?_) m
  simpa only [smul_eq_mul, hf] using hasSum_etaProduct a b c e he τ

private def Rep (N : ℕ) (L : List ℤ) (F : PowerSeries ℤ) : Prop := ∀ m, m < N → L.getD m 0 =
  PowerSeries.coeff m F

private def oneL (N : ℕ) : List ℤ := (List.range N).map fun m => if m = 0 then 1 else 0
private def XpowL (N e : ℕ) : List ℤ := (List.range N).map fun m => if m = e then 1 else 0

private def facL (N k : ℕ) : List ℤ := (List.range N).map fun m => (if m = 0 then 1 else 0) - (if m
  = k then 1 else 0)
private def mulL (N : ℕ) (u v : List ℤ) : List ℤ :=
  (List.range N).map fun m => ∑ i ∈ Finset.range (m + 1), u.getD i 0 * v.getD (m - i) 0
private def powL (N : ℕ) (u : List ℤ) : ℕ → List ℤ
  | 0 => oneL N
  | n + 1 => mulL N (powL N u n) u
private def expandL (N k : ℕ) (u : List ℤ) : List ℤ :=
  (List.range N).map fun m => if k ∣ m then u.getD (m / k) 0 else 0

private def etaL (N : ℕ) : List ℤ := ((List.range N).map fun n => facL N (n + 1)).foldr (mulL N)
  (oneL N)

private theorem getD_map_range {N m : ℕ} (hm : m < N) (g : ℕ → ℤ) : ((List.range N).map g).getD m 0
  = g m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
  rfl

private theorem Rep.one (N : ℕ) : Rep N (oneL N) 1 := fun m hm => by
  rw [oneL, getD_map_range hm, PowerSeries.coeff_one]

private theorem Rep.Xpow (N e : ℕ) : Rep N (XpowL N e) (PowerSeries.X ^ e) := fun m hm => by
  rw [XpowL, getD_map_range hm, PowerSeries.coeff_X_pow]

private theorem Rep.fac (N k : ℕ) : Rep N (facL N k) (1 - PowerSeries.X ^ k) := fun m hm => by
  rw [facL, getD_map_range hm, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]

private theorem Rep.mul {N : ℕ} {u v : List ℤ} {F G : PowerSeries ℤ} (hu : Rep N u F) (hv : Rep N v
  G) :
    Rep N (mulL N u v) (F * G) := fun m hm => by
  rw [mulL, getD_map_range hm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [hu i (by omega), hv (m - i) (by omega)]

private theorem Rep.pow {N : ℕ} {u : List ℤ} {F : PowerSeries ℤ} (hu : Rep N u F) (n : ℕ) : Rep N
  (powL N u n) (F ^ n) := by
  induction n with
  | zero => simpa [powL] using Rep.one N
  | succ n ih => rw [powL, pow_succ]; exact ih.mul hu

private theorem Rep.expand {N k : ℕ} (hk : k ≠ 0) {u : List ℤ} {F : PowerSeries ℤ} (hu : Rep N u F)
  :
    Rep N (expandL N k u) (PowerSeries.expand k hk F) := fun m hm => by
  rw [expandL, getD_map_range hm, PowerSeries.coeff_expand]
  split_ifs with h
  · exact hu _ (lt_of_le_of_lt (Nat.div_le_self m k) hm)
  · rfl

private theorem Rep.foldr {N : ℕ} (l : List (List ℤ × PowerSeries ℤ)) (hl : ∀ p ∈ l, Rep N p.1 p.2)
  :
    Rep N ((l.map Prod.fst).foldr (mulL N) (oneL N)) ((l.map Prod.snd).prod) := by
  induction l with
  | nil => simpa using Rep.one N
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    exact (hl p (List.mem_cons_self)).mul (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

private def Cong (m : ℕ) (G : PowerSeries ℤ) : Prop := (PowerSeries.X : PowerSeries ℤ) ^ (m + 1) ∣
  G - 1

private theorem Cong.mul {m : ℕ} {G H : PowerSeries ℤ} (hG : Cong m G) (hH : Cong m H) : Cong m (G
  * H) := by
  have : G * H - 1 = (G - 1) * H + (H - 1) := by ring
  rw [Cong, this]
  exact dvd_add (hG.mul_right _) hH

private theorem Cong.one (m : ℕ) : Cong m 1 := by simp [Cong]

private theorem Cong.prod {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → PowerSeries ℤ} (hg : ∀ i ∈ s,
  Cong m (g i)) :
    Cong m (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong.one m
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hg i (Finset.mem_insert_self i s)).mul (ih fun j hj => hg j (Finset.mem_insert_of_mem
      hj))

private theorem Cong.one_sub_X_pow {m n : ℕ} (hn : m + 1 ≤ n + 1) : Cong m (1 - PowerSeries.X ^ (n
  + 1)) := by
  rw [Cong, sub_sub_cancel_left, dvd_neg]
  exact pow_dvd_pow _ hn

private theorem coeff_mul_of_cong {m : ℕ} {G : PowerSeries ℤ} (hG : Cong m G) (H : PowerSeries ℤ) :
    PowerSeries.coeff m (H * G) = PowerSeries.coeff m H := by
  obtain ⟨K, hK⟩ := hG
  have : G = 1 + PowerSeries.X ^ (m + 1) * K := by rw [← hK]; ring
  rw [this, mul_add, mul_one, map_add, ← mul_assoc, mul_comm H, mul_assoc,
    PowerSeries.coeff_X_pow_mul',
    if_neg (by omega), add_zero]

private theorem coeff_prod_eq (m : ℕ) (s : Finset ℕ) (hs : Finset.range (m + 1) ⊆ s) :
    PowerSeries.coeff m (∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) =
      PowerSeries.coeff m (∏ n ∈ Finset.range (m + 1), ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n +
        1))) := by
  rw [← Finset.prod_sdiff hs, mul_comm]
  apply coeff_mul_of_cong
  apply Cong.prod
  intro n hn
  rw [Finset.mem_sdiff, Finset.mem_range, not_lt] at hn
  exact Cong.one_sub_X_pow (by omega)

open Filter Topology in
open scoped PowerSeries.WithPiTopology in
private theorem coeff_etaProd_eq (m : ℕ) :
    PowerSeries.coeff m etaProd =
      PowerSeries.coeff m (∏ n ∈ Finset.range (m + 1), ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n +
        1))) := by
  have hmult := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have h1 : Tendsto (fun s : Finset ℕ => ∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1)))
    atTop
      (𝓝 etaProd) := hmult.hasProd
  have h2 := ((PowerSeries.WithPiTopology.continuous_coeff ℤ m).tendsto _).comp h1
  have h3 : Tendsto (fun s : Finset ℕ =>
      PowerSeries.coeff m (∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1)))) atTop
      (𝓝 (PowerSeries.coeff m (∏ n ∈ Finset.range (m + 1), ((1 : PowerSeries ℤ) - PowerSeries.X ^
        (n + 1))))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Finset.range (m + 1))] with s hs
    exact (coeff_prod_eq m s hs).symm
  exact tendsto_nhds_unique h2 h3

private theorem coeff_etaProd_eq_coeff_prod (N m : ℕ) (hm : m < N) :
    PowerSeries.coeff m etaProd =
      PowerSeries.coeff m (∏ n ∈ Finset.range N, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1)))
        := by
  rw [coeff_etaProd_eq]
  exact (coeff_prod_eq m (Finset.range N) (Finset.range_subset_range.mpr hm)).symm

private theorem Rep.etaProd (N : ℕ) : Rep N (etaL N) etaProd := by
  have h := Rep.foldr (N := N) ((List.range N).map fun n => (facL N (n + 1), (1 : PowerSeries ℤ) -
    PowerSeries.X ^ (n + 1)))
    (fun p hp => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hp
      exact Rep.fac N (n + 1))
  rw [List.map_map, List.map_map] at h
  have h' : Rep N (etaL N) (((List.range N).map fun n => (1 : PowerSeries ℤ) - PowerSeries.X ^ (n +
    1)).prod) := h
  intro m hm
  have hr : Finset.range N = (List.range N).toFinset := by ext; simp
  rw [coeff_etaProd_eq_coeff_prod N m hm, hr, List.prod_toFinset _ List.nodup_range]
  exact h' m hm

private theorem Rep.S (N a b c e : ℕ) :
    Rep N (mulL N (XpowL N e) (mulL N (mulL N (powL N (etaL N) a) (expandL N 2 (powL N (etaL N) b)))
      (expandL N 4 (powL N (etaL N) c)))) (S a b c e) :=
  (Rep.Xpow N e).mul ((((Rep.etaProd N).pow a).mul (Rep.expand two_ne_zero ((Rep.etaProd N).pow
    b))).mul
    (Rep.expand (by norm_num) ((Rep.etaProd N).pow c)))

end ARails
end ModularCurve

namespace ModularCurve
namespace ARails

open Complex
open scoped MatrixGroups
local notation "𝕢" => Function.Periodic.qParam

private theorem QS_eisenstein4 : QS (eisenstein4.map (Int.castRingHom ℂ)) (fun τ => ModularForm.E₄
  τ) := fun τ => by
  simpa [PowerSeries.coeff_map] using hasSum_coeff_eisenstein4_qParam τ

private theorem QS_S (a b c e : ℕ) (he : a + 2 * b + 4 * c = 24 * e) :
    QS ((S a b c e).map (Int.castRingHom ℂ)) (fun τ => ModularForm.eta (τ : ℂ) ^ a *
      ModularForm.eta (2 * (τ : ℂ)) ^ b * ModularForm.eta (4 * (τ : ℂ)) ^ c) := fun τ => by
  simpa [PowerSeries.coeff_map] using hasSum_etaProduct a b c e he τ

private noncomputable def SE : PowerSeries ℤ := ModularCurve.eisenstein4 * S 16 8 16 4

private theorem hasSum_LHS (z : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m SE : ℤ) : ℂ) * 𝕢 1 (z : ℂ) ^ m)
      (ModularForm.E₄ z * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (2 * (z : ℂ)) ^ 8 *
        ModularForm.eta (4 * (z : ℂ)) ^ 16)) := by
  have h := (QS_eisenstein4.mul (QS_S 16 8 16 4 (by norm_num))) z
  rw [← map_mul] at h
  simpa only [PowerSeries.coeff_map, eq_intCast, SE] using h

private def e4L : List ℤ := [1, 240, 2160, 6720, 17520, 30240, 60480, 82560, 140400, 181680,
  272160, 319680, 490560]

private theorem Rep.eisenstein4 : Rep 13 e4L eisenstein4 := by
  intro m hm
  rw [ModularCurve.eisenstein4, PowerSeries.coeff_mk]
  interval_cases m <;> decide

private def etaL13 : List ℤ := [1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1]

set_option maxRecDepth 20000 in
private theorem etaL_thirteen : etaL 13 = etaL13 := by decide +kernel

private def u8L : List ℤ := [1, -8, 20, 0, -70, 64, 56, 0, -125, -160, 308, 0, 110]

set_option maxRecDepth 20000 in
private theorem u8L_eq : powL 13 etaL13 8 = u8L := by decide +kernel

private theorem Rep_u8 : Rep 13 u8L (etaProd ^ 8) := by
  rw [← u8L_eq, ← etaL_thirteen]
  exact (Rep.etaProd 13).pow 8

private theorem four_ne_zero' : (4 : ℕ) ≠ 0 := by norm_num

private def SEL : List ℤ := [0, 0, 0, 0, 1, 224, -1584, -4992, 70712, -152256, -365248, 1652992,
  -52788]
private def S1L : List ℤ := [0, 0, 0, 0, 1, 0, -48, 0, 1080, 0, -15040, 0, 143820]
private def S2L : List ℤ := [0, 0, 0, 0, 0, 1, -8, -4, 192, -314, -1824, 5368, 7168]
private def S3L : List ℤ := [0, 0, 0, 0, 0, 0, 1, -16, 104, -320, 228, 1760, -7040]

set_option maxRecDepth 20000 in
private theorem SEL_eq : mulL 13 e4L (mulL 13 (XpowL 13 4) (mulL 13 (mulL 13 (powL 13 u8L 2)
  (expandL 13 2 u8L))
    (expandL 13 4 (powL 13 u8L 2)))) = SEL := by decide +kernel
set_option maxRecDepth 20000 in
private theorem S1L_eq :
    mulL 13 (XpowL 13 4) (expandL 13 2 (powL 13 u8L 6)) = S1L := by
  decide +kernel
set_option maxRecDepth 20000 in
private theorem S2L_eq : mulL 13 (XpowL 13 5) (mulL 13 (mulL 13 u8L (expandL 13 2 (powL 13 u8L 3)))
    (expandL 13 4 (powL 13 u8L 2))) = S2L := by decide +kernel
set_option maxRecDepth 20000 in
private theorem S3L_eq : mulL 13 (XpowL 13 6) (mulL 13 (powL 13 u8L 2) (expandL 13 4 (powL 13 u8L
  4))) = S3L := by
  decide +kernel

private theorem SE_eq : SE = ModularCurve.eisenstein4 * (PowerSeries.X ^ 4 * ((etaProd ^ 8) ^ 2 *
    PowerSeries.expand 2 two_ne_zero (etaProd ^ 8) * PowerSeries.expand 4 four_ne_zero' ((etaProd ^
      8) ^ 2))) := by
  rw [SE, S, ← pow_mul]
private theorem S1_eq : S 0 48 0 4 = PowerSeries.X ^ 4 * PowerSeries.expand 2 two_ne_zero ((etaProd
  ^ 8) ^ 6) := by
  rw [S, ← pow_mul]
  simp
private theorem S2_eq : S 8 24 16 5 = PowerSeries.X ^ 5 * (etaProd ^ 8 *
    PowerSeries.expand 2 two_ne_zero ((etaProd ^ 8) ^ 3) * PowerSeries.expand 4 four_ne_zero'
      ((etaProd ^ 8) ^ 2)) := by
  rw [S, ← pow_mul, ← pow_mul]
private theorem S3_eq : S 16 0 32 6 = PowerSeries.X ^ 6 * ((etaProd ^ 8) ^ 2 *
    PowerSeries.expand 4 four_ne_zero' ((etaProd ^ 8) ^ 4)) := by
  rw [S, ← pow_mul, ← pow_mul]
  simp

private theorem Rep_SE : Rep 13 SEL SE := by
  rw [SE_eq, ← SEL_eq]
  exact Rep.eisenstein4.mul ((Rep.Xpow 13 4).mul (((Rep_u8.pow 2).mul (Rep.expand two_ne_zero
    Rep_u8)).mul
    (Rep.expand four_ne_zero' (Rep_u8.pow 2))))
private theorem Rep_S1 : Rep 13 S1L (S 0 48 0 4) := by
  rw [S1_eq, ← S1L_eq]
  exact (Rep.Xpow 13 4).mul (Rep.expand two_ne_zero (Rep_u8.pow 6))
private theorem Rep_S2 : Rep 13 S2L (S 8 24 16 5) := by
  rw [S2_eq, ← S2L_eq]
  exact (Rep.Xpow 13 5).mul ((Rep_u8.mul (Rep.expand two_ne_zero (Rep_u8.pow 3))).mul
    (Rep.expand four_ne_zero' (Rep_u8.pow 2)))
private theorem Rep_S3 : Rep 13 S3L (S 16 0 32 6) := by
  rw [S3_eq, ← S3L_eq]
  exact (Rep.Xpow 13 6).mul ((Rep_u8.pow 2).mul (Rep.expand four_ne_zero' (Rep_u8.pow 4)))

private theorem lists_agree : ∀ m, m < 13 → SEL.getD m 0 - (S1L.getD m 0 + 224 * S2L.getD m 0 + 256
  * S3L.getD m 0) = 0 := by
  decide

private theorem coeff_agree (m : ℕ) (hm : m < 13) :
    (PowerSeries.coeff m SE : ℤ) -
      (PowerSeries.coeff m (S 0 48 0 4) + 224 * PowerSeries.coeff m (S 8 24 16 5) +
        256 * PowerSeries.coeff m (S 16 0 32 6)) = 0 := by
  rw [← Rep_SE m hm, ← Rep_S1 m hm, ← Rep_S2 m hm, ← Rep_S3 m hm]
  exact lists_agree m hm

private theorem A2p_weight24 (z : UpperHalfPlane) :
    ModularForm.E₄ z * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (2 * (z : ℂ)) ^ 8 *
        ModularForm.eta (4 * (z : ℂ)) ^ 16) =
      ModularForm.eta (z : ℂ) ^ 0 * ModularForm.eta (2 * (z : ℂ)) ^ 48 * ModularForm.eta (4 * (z :
        ℂ)) ^ 0 +
        224 * (ModularForm.eta (z : ℂ) ^ 8 * ModularForm.eta (2 * (z : ℂ)) ^ 24 * ModularForm.eta
          (4 * (z : ℂ)) ^ 16) +
        256 * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (2 * (z : ℂ)) ^ 0 * ModularForm.eta
          (4 * (z : ℂ)) ^ 32) := by

  obtain ⟨G, hG⟩ := exists_gamma0_qExpansion_eq_of_levelOne 4 ModularForm.E₄
  obtain ⟨f0, hf0⟩ := exists_gamma0_four_apply_eq_eta_pow_mul 16 8 16 (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  obtain ⟨f1, hf1⟩ := exists_gamma0_four_apply_eq_eta_pow_mul 0 48 0 (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  obtain ⟨f2, hf2⟩ := exists_gamma0_four_apply_eq_eta_pow_mul 8 24 16 (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  obtain ⟨f3, hf3⟩ := exists_gamma0_four_apply_eq_eta_pow_mul 16 0 32 (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by norm_num)
  have hGz : ∀ z : UpperHalfPlane, G z = ModularForm.E₄ z := fun z => congrFun hG z

  let F : ModularForm (CongruenceSubgroup.Gamma0 4) 24 :=
    ModularForm.mcast (by norm_num) (G.mul (toMF f0)) -
      (ModularForm.mcast (by norm_num) (toMF f1) + (224 : ℂ) • ModularForm.mcast (by norm_num)
        (toMF f2) +
        (256 : ℂ) • ModularForm.mcast (by norm_num) (toMF f3))
  have hFz : ∀ z : UpperHalfPlane, F z = G z * f0 z - (f1 z + 224 * f2 z + 256 * f3 z) := fun z =>
    rfl

  let c : ℕ → ℂ := fun m => ((PowerSeries.coeff m SE : ℤ) : ℂ) -
    (((PowerSeries.coeff m (S 0 48 0 4) : ℤ) : ℂ) + 224 * ((PowerSeries.coeff m (S 8 24 16 5) : ℤ)
      : ℂ) +
      256 * ((PowerSeries.coeff m (S 16 0 32 6) : ℤ) : ℂ))
  have hF : ∀ z : UpperHalfPlane, HasSum (fun m : ℕ => c m • 𝕢 1 (z : ℂ) ^ m) (F z) := by
    intro z
    have h := (hasSum_LHS z).sub (((hasSum_etaProduct 0 48 0 4 (by norm_num) z).add
      ((hasSum_etaProduct 8 24 16 5 (by norm_num) z).mul_left 224)).add
      ((hasSum_etaProduct 16 0 32 6 (by norm_num) z).mul_left 256))
    rw [hFz, hGz, hf0, hf1, hf2, hf3]
    convert h using 1 <;> try with_reducible_and_instances rfl
    funext m
    simp only [c, smul_eq_mul]
    ring

  have hF0 : F = 0 := by
    refine ModularForm.sturm_bound_Gamma0 4 F (fun n hn => ?_)
    rw [index_Gamma0_four] at hn
    norm_num at hn
    rw [← ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma0 4) hF n]
    have hz := coeff_agree n (by omega)
    have : c n = (((PowerSeries.coeff n SE : ℤ) -
      (PowerSeries.coeff n (S 0 48 0 4) + 224 * PowerSeries.coeff n (S 8 24 16 5) +
        256 * PowerSeries.coeff n (S 16 0 32 6)) : ℤ) : ℂ) := by
      simp only [c]; push_cast; ring
    rw [this, hz, Int.cast_zero]
  have h0 : F z = 0 := by rw [hF0]; rfl
  rw [hFz, hGz, hf0, hf1, hf2, hf3] at h0
  linear_combination h0

end ARails
end ModularCurve



/-- The Eisenstein series `E₄` times the eta product
`η(z)¹⁶ η(2z)⁸ η(4z)¹⁶` equals `η(2z)⁴⁸ + 224 η(z)⁸ η(2z)²⁴ η(4z)¹⁶
+ 256 η(z)¹⁶ η(4z)³²`. -/
public theorem ModularForm.E4_mul_etaProduct_eq (z : UpperHalfPlane) :
    ModularForm.E₄ z * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (2 * (z : ℂ)) ^ 8 *
        ModularForm.eta (4 * (z : ℂ)) ^ 16) =
      ModularForm.eta (2 * (z : ℂ)) ^ 48 +
        224 * (ModularForm.eta (z : ℂ) ^ 8 * ModularForm.eta (2 * (z : ℂ)) ^ 24 *
          ModularForm.eta (4 * (z : ℂ)) ^ 16) +
        256 * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (4 * (z : ℂ)) ^ 32) := by
  have h := ModularCurve.ARails.A2p_weight24 z
  simp only [pow_zero, mul_one, one_mul] at h
  exact h

end
