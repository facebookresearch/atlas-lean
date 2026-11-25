/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularForm_HeckeOperator.lean`,
`Definitions/Def_CohCarrier_Level.lean`,
`Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean`,
`Theorems/Thm_ModularForm_mdifferentiable_heckeU.lean`,
`Theorems/Thm_CuspFormClass_isZeroAt_heckeU.lean`,
`Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean`,
`Theorems/Thm_CuspForm_stableU.lean`,
`Theorems/Thm_ModularFormClass_qCoeff_heckeU.lean` and
`Theorems/Thm_CuspForm_heckeULinH_comm.lean`
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

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import MathlibExt.NumberTheory.ModularForms.GammaH
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.NumberTheory.ModularForms.OldForms
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.GroupTheory.Transfer
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open scoped MatrixGroups ModularForm

namespace CongruenceSubgroup

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

def Gamma0Upper (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g | (g 0 1 : ZMod ℓ) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    have h := (Matrix.two_mul_expl a.1 b.1).2.1
    simp only [coe_mul] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [SL2_inv_expl a]
    simpa using ha

@[simp]
theorem mem_Gamma0Upper {ℓ : ℕ} {A : SL(2, ℤ)} : A ∈ Gamma0Upper ℓ ↔ (A 0 1 : ZMod ℓ) = 0 :=
  Iff.rfl


def conjUpperMat (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) : SL(2, ℤ) :=
  ⟨!![A 0 0, A 0 1 / ℓ; A 1 0 * ℓ, A 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hbc : A 0 1 / ℓ * (A 1 0 * ℓ) = A 0 1 * A 1 0 := by
      rw [mul_comm (A 1 0) _, ← mul_assoc, Int.ediv_mul_cancel h]
    rw [hbc]
    exact hdet⟩

theorem conjUpperMat_mul (A B : SL(2, ℤ)) (hA : (ℓ : ℤ) ∣ A 0 1) (hB : (ℓ : ℤ) ∣ B 0 1)
    (hAB : (ℓ : ℤ) ∣ (A * B) 0 1) :
    conjUpperMat ℓ (A * B) hAB = conjUpperMat ℓ A hA * conjUpperMat ℓ B hB := by
  have h1 : A 0 1 / ℓ * (B 1 0 * ℓ) = A 0 1 * B 1 0 := by
    rw [mul_comm (B 1 0) _, ← mul_assoc, Int.ediv_mul_cancel hA]
  have h2 : (A 0 0 * B 0 1 + A 0 1 * B 1 1) / ℓ = A 0 0 * (B 0 1 / ℓ) + A 0 1 / ℓ * B 1 1 := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_right hA _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 0 1) (B 1 1), Int.mul_ediv_assoc _ hA, mul_comm (B 1 1)]
  have h3 : A 1 0 * ℓ * (B 0 1 / ℓ) = A 1 0 * B 0 1 := by
    rw [mul_assoc, Int.mul_ediv_cancel' hB]
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.SpecialLinearGroup.coe_mul] <;>
    simp [conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hmul, h2, h1, h3]
  ring

@[simp] theorem conjUpperMat_apply_11 (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 1 1 = A 1 1 := by
  simp [conjUpperMat]

@[simp] theorem conjUpperMat_apply_10 (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 1 0 = A 1 0 * ℓ := by
  simp [conjUpperMat]

abbrev GammaHUpper : Subgroup ↥(GammaH M H) := (Gamma0Upper ℓ).subgroupOf (GammaH M H)

theorem dvd_of_mem_GammaHUpper (γ : ↥(GammaHUpper M H ℓ)) : (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := by
  have h : ((γ : ↥(GammaH M H)) : SL(2, ℤ)) ∈ Gamma0Upper ℓ := Subgroup.mem_subgroupOf.mp γ.2
  rw [mem_Gamma0Upper] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

theorem conjUpperMat_mem (γ : ↥(GammaHUpper M H ℓ)) :
    conjUpperMat ℓ (γ : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M H ℓ γ) ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := (mem_GammaH_iff M).mp (γ : ↥(GammaH M H)).2
  rw [mem_GammaH_iff M]
  refine ⟨?_, ?_⟩
  · rw [Gamma0_mem, conjUpperMat_apply_10, Int.cast_mul, Gamma0_mem.mp hγ0, zero_mul]
  · convert hγH using 1
    ext
    simp only [val_gamma0Units, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, conjUpperMat_apply_11]

def conjL : ↥(GammaHUpper M H ℓ) →* ↥(GammaH M H) where
  toFun γ := ⟨conjUpperMat ℓ (γ : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M H ℓ γ),
    conjUpperMat_mem M H ℓ γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjUpperMat]
  map_mul' γ δ :=
    Subtype.ext (conjUpperMat_mul ℓ (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M H ℓ γ)
      (dvd_of_mem_GammaHUpper M H ℓ δ) (dvd_of_mem_GammaHUpper M H ℓ (γ * δ)))



public instance gammaHUpper_finiteIndex [NeZero M] [NeZero ℓ] :
    (GammaHUpper M H ℓ).FiniteIndex := by
  have : ((Gamma (M * ℓ)).subgroupOf (GammaH M H)).FiniteIndex := inferInstance
  refine Subgroup.finiteIndex_of_le (H := (Gamma (M * ℓ)).subgroupOf (GammaH M H)) ?_
  intro γ hγ
  have hγ2 := Subgroup.mem_subgroupOf.mp hγ
  refine Subgroup.mem_subgroupOf.mpr ?_
  rw [mem_Gamma0Upper]
  have h01 : (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod (M * ℓ)) = 0 := (Gamma_mem.mp hγ2).2.1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr
    (dvd_trans (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) by exact_mod_cast dvd_mul_left ℓ M)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (M * ℓ)).mp h01))

variable (M : ℕ) in
theorem gamma0Units_surjective [NeZero M] : Function.Surjective (gamma0Units M) := by
  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ) - 1 : ℤ) : ZMod M) =
    0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k; (M : ℤ), ((u : ZMod M).val :
    ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Gamma0Map]
  simp [γ]


end CongruenceSubgroup


namespace ModularForm

noncomputable def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] :=
      rfl

noncomputable def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

@[simp] theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeMatrix, hp]

@[simp] theorem heckeMatrix_zero (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]


theorem det_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) : ((heckeMatrix p j).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeMatrix hp, Matrix.det_fin_two_of]
  ring


theorem det_heckeMatrix_pos (p j : ℕ) : 0 < ((heckeMatrix p j).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp


theorem denom_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeMatrix hp]


theorem coe_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeMatrix hp]


theorem σ_heckeMatrix (p j : ℕ) : UpperHalfPlane.σ (heckeMatrix p j) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, ite_eq_left (det_heckeMatrix_pos p j)]


theorem slash_heckeMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeMatrix, det_heckeMatrix hp, denom_heckeMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]


noncomputable def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

/-- The prime-index Hecke formula `T_p f = U_p f + f ∣[k] diag(p, 1)`, that is,
`(p : ℂ)⁻¹ * ∑ j < p, f ((τ + j) / p) + p ^ (k - 1) * f (p * τ)` (see `heckeTPrime_apply`).
It is stated only for a prime `p`: at a composite index the Hecke operator has further divisor
terms, so this two-term formula is not `T_n` in general. -/
noncomputable def heckeTPrime (k : ℤ) (p : ℕ) [Fact p.Prime] (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

theorem heckeU_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeU k p f = ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j := rfl

theorem heckeTPrime_eq_heckeU_add (k : ℤ) (p : ℕ) [Fact p.Prime] (f : UpperHalfPlane → ℂ) :
    heckeTPrime k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p := rfl

theorem heckeTPrime_def (k : ℤ) (p : ℕ) [Fact p.Prime] (f : UpperHalfPlane → ℂ) :
    heckeTPrime k p f =
      (∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j) + f ∣[k] heckeDiagMatrix p := rfl

@[simp] theorem heckeU_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by
  simp [heckeU]

theorem heckeU_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeU k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeU, Finset.sum_apply, slash_heckeMatrix_apply k hp, Finset.mul_sum]

theorem heckeTPrime_apply (k : ℤ) (p : ℕ) [hp : Fact p.Prime] (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    heckeTPrime k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)
      + (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [heckeTPrime, Pi.add_apply, heckeU_apply k hp.out.ne_zero,
    slash_heckeDiagMatrix_apply k hp.out.ne_zero]

@[simp] theorem heckeU_zero (k : ℤ) (p : ℕ) : heckeU k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeU]

@[simp] theorem heckeTPrime_zero (k : ℤ) (p : ℕ) [Fact p.Prime] :
    heckeTPrime k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeTPrime]

theorem heckeU_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f + g) = heckeU k p f + heckeU k p g := by
  simp [heckeU, Finset.sum_add_distrib]

theorem heckeTPrime_add (k : ℤ) (p : ℕ) [Fact p.Prime] (f g : UpperHalfPlane → ℂ) :
    heckeTPrime k p (f + g) = heckeTPrime k p f + heckeTPrime k p g := by
  simp only [heckeTPrime, heckeU_add, SlashAction.add_slash]
  abel

theorem heckeU_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeU k p (c • f) = c • heckeU k p f := by
  simp only [heckeU, ModularForm.smul_slash, σ_heckeMatrix, ContinuousAlgEquiv.refl_apply,
    Finset.smul_sum]

theorem heckeTPrime_smul (k : ℤ) (p : ℕ) [Fact p.Prime] (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeTPrime k p (c • f) = c • heckeTPrime k p f := by
  rw [heckeTPrime, heckeTPrime, heckeU_smul, ModularForm.smul_slash, σ_heckeDiagMatrix,
    ContinuousAlgEquiv.refl_apply, smul_add]

theorem heckeU_neg (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : heckeU k p (-f) = -heckeU k p f := by
  simp [heckeU, Finset.sum_neg_distrib]

theorem heckeTPrime_neg (k : ℤ) (p : ℕ) [Fact p.Prime] (f : UpperHalfPlane → ℂ) :
    heckeTPrime k p (-f) = -heckeTPrime k p f := by
  simp only [heckeTPrime, heckeU_neg, SlashAction.neg_slash, neg_add]

theorem heckeU_sub (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f - g) = heckeU k p f - heckeU k p g := by
  rw [sub_eq_add_neg, heckeU_add, heckeU_neg, ← sub_eq_add_neg]

theorem heckeTPrime_sub (k : ℤ) (p : ℕ) [Fact p.Prime] (f g : UpperHalfPlane → ℂ) :
    heckeTPrime k p (f - g) = heckeTPrime k p f - heckeTPrime k p g := by
  rw [sub_eq_add_neg, heckeTPrime_add, heckeTPrime_neg, ← sub_eq_add_neg]

/-- The action of `heckeTPrime k p` on `q`-expansion coefficients, for a prime `p`:
`n ↦ a (n * p) + p ^ (k - 1) * a (n / p)`, where the second term appears only when `p ∣ n`. -/
noncomputable def coeffHeckeTPrime (k : ℤ) (p : ℕ) [Fact p.Prime] (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

noncomputable def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

theorem coeffHeckeTPrime_apply (k : ℤ) (p : ℕ) [Fact p.Prime] (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeTPrime k p a n = a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 :=
  rfl

theorem coeffHeckeU_apply (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : coeffHeckeU p a n = a (n * p) := rfl

theorem coeffHeckeTPrime_of_dvd (k : ℤ) {p n : ℕ} [Fact p.Prime] (h : p ∣ n) (a : ℕ → ℂ) :
    coeffHeckeTPrime k p a n = a (n * p) + (p : ℂ) ^ (k - 1) * a (n / p) := by
  rw [coeffHeckeTPrime, ite_eq_left h]

theorem coeffHeckeTPrime_of_not_dvd (k : ℤ) {p n : ℕ} [Fact p.Prime] (h : ¬ p ∣ n)
    (a : ℕ → ℂ) : coeffHeckeTPrime k p a n = a (n * p) := by
  rw [coeffHeckeTPrime, ite_eq_right h, add_zero]

theorem coeffHeckeTPrime_eq_coeffHeckeU_add (k : ℤ) (p : ℕ) [Fact p.Prime] (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeTPrime k p a n =
      coeffHeckeU p a n + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 :=
  rfl

theorem coeffHeckeTPrime_add (k : ℤ) (p : ℕ) [Fact p.Prime] (a b : ℕ → ℂ) :
    coeffHeckeTPrime k p (a + b) = coeffHeckeTPrime k p a + coeffHeckeTPrime k p b := by
  funext n
  simp only [coeffHeckeTPrime, Pi.add_apply]
  split_ifs <;> ring

theorem coeffHeckeTPrime_smul (k : ℤ) (p : ℕ) [Fact p.Prime] (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeTPrime k p (c • a) = c • coeffHeckeTPrime k p a := by
  funext n
  simp only [coeffHeckeTPrime, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem coeffHeckeU_add (p : ℕ) (a b : ℕ → ℂ) :
    coeffHeckeU p (a + b) = coeffHeckeU p a + coeffHeckeU p b := rfl

theorem coeffHeckeU_smul (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeU p (c • a) = c • coeffHeckeU p a := rfl


end ModularForm

namespace ModularFormHeckeUQExp

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology
open ModularForm ModularFormClass

section Matrices

variable (p j : ℕ)

theorem heckeMatrix_one_zero :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeMatrix hp]; rfl

theorem heckeDiagMatrix_one_zero :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeDiagMatrix hp]; rfl

end Matrices

section Regularity

variable {f : ℍ → ℂ} (k : ℤ) (p : ℕ)

theorem mdifferentiable_heckeU (hf : MDiff f) : MDiff (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => MDiff g) (fun _ _ ha hb => ha.add hb)
    mdifferentiable_const (fun _ _ => hf.slash k _)

theorem mdifferentiable_heckeTPrime [Fact p.Prime] (hf : MDiff f) : MDiff (heckeTPrime k p f) :=
  (mdifferentiable_heckeU k p hf).add (hf.slash k _)

theorem isBoundedAtImInfty_heckeU (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsBoundedAtImInfty g)
    (fun _ _ ha hb => ha.add hb) UpperHalfPlane.zero_form_isBoundedAtImInfty
    (fun j _ => hf.slash k (heckeMatrix_one_zero p j))

theorem isBoundedAtImInfty_heckeTPrime [Fact p.Prime] (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeTPrime k p f) :=
  (isBoundedAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

theorem isZeroAtImInfty_heckeU (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsZeroAtImInfty g)
    (fun _ _ ha hb => ha.add hb) (zero_zeroAtFilter atImInfty)
    (fun j _ => hf.slash k (heckeMatrix_one_zero p j))

theorem isZeroAtImInfty_heckeTPrime [Fact p.Prime] (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeTPrime k p f) :=
  (isZeroAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

theorem apply_eq_of_coe_eq_add_nat (hf : Periodic (f ∘ ofComplex) 1) {τ₁ τ₂ : ℍ} (m : ℕ)
    (h : (τ₁ : ℂ) = τ₂ + m) : f τ₁ = f τ₂ := by
  have h1 : (f ∘ ofComplex) ((τ₂ : ℂ) + m) = (f ∘ ofComplex) (τ₂ : ℂ) := by
    have := hf.nat_mul m
    rw [mul_one] at this
    exact this (τ₂ : ℂ)
  simp only [comp_apply] at h1
  rw [← h, ofComplex_apply, ofComplex_apply] at h1
  exact h1

variable {p} in
theorem heckeMatrix_smul_vadd (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    heckeMatrix p j • ((1 : ℝ) +ᵥ τ) = heckeMatrix p (j + 1) • τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeMatrix_smul hp, coe_heckeMatrix_smul hp, coe_vadd]
  push_cast
  ring

variable {p} in
theorem coe_heckeMatrix_smul_self (hp : p ≠ 0) (τ : ℍ) :
    ((heckeMatrix p p • τ : ℍ) : ℂ) = (heckeMatrix p 0 • τ : ℍ) + (1 : ℕ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [coe_heckeMatrix_smul hp, coe_heckeMatrix_smul hp]
  field_simp
  push_cast
  ring

variable {p} in
theorem coe_heckeDiagMatrix_smul_vadd (hp : p ≠ 0) (τ : ℍ) :
    ((heckeDiagMatrix p • ((1 : ℝ) +ᵥ τ) : ℍ) : ℂ) = (heckeDiagMatrix p • τ : ℍ) + (p : ℕ) := by
  rw [coe_heckeDiagMatrix_smul hp, coe_heckeDiagMatrix_smul hp, coe_vadd]
  push_cast
  ring

variable {p} in
theorem sum_heckeMatrix_smul_vadd (hp : p ≠ 0) (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    ∑ j ∈ Finset.range p, f (heckeMatrix p j • ((1 : ℝ) +ᵥ τ))
      = ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeMatrix_smul_vadd hp]
  have h0 := Finset.sum_range_succ' (fun j => f (heckeMatrix p j • τ)) p
  have h1 := Finset.sum_range_succ (fun j => f (heckeMatrix p j • τ)) p
  rw [apply_eq_of_coe_eq_add_nat hf 1 (coe_heckeMatrix_smul_self hp τ)] at h1
  exact add_right_cancel (h0.symm.trans h1)

theorem heckeU_vadd (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    heckeU k p f ((1 : ℝ) +ᵥ τ) = heckeU k p f τ := by
  by_cases hp : p = 0
  · simp only [hp, heckeU_zero_left, Pi.zero_apply]
  · rw [heckeU_apply k hp, heckeU_apply k hp, sum_heckeMatrix_smul_vadd hp hf]

theorem heckeTPrime_vadd [hp : Fact p.Prime] (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    heckeTPrime k p f ((1 : ℝ) +ᵥ τ) = heckeTPrime k p f τ := by
  rw [heckeTPrime_apply k p, heckeTPrime_apply k p, sum_heckeMatrix_smul_vadd hp.out.ne_zero hf,
    apply_eq_of_coe_eq_add_nat hf p (coe_heckeDiagMatrix_smul_vadd hp.out.ne_zero τ)]

theorem periodic_comp_ofComplex_of_vadd {g : ℍ → ℂ} (hg : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) :
    Periodic (g ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < im w
  · have hw' : 0 < im (w + 1) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert hg ⟨w, hw⟩ using 2
    apply UpperHalfPlane.ext
    simp [add_comm]
  · have hw1 : im (w + 1) ≤ 0 := by simpa using hw
    have hw0 : im w ≤ 0 := not_lt.mp hw
    simp only [comp_apply, ofComplex_apply_eq_of_im_nonpos hw1 hw0]

theorem periodic_heckeU_comp_ofComplex (hf : Periodic (f ∘ ofComplex) 1) :
    Periodic (heckeU k p f ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (heckeU_vadd k p hf)

theorem periodic_heckeTPrime_comp_ofComplex [Fact p.Prime] (hf : Periodic (f ∘ ofComplex) 1) :
    Periodic (heckeTPrime k p f ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (heckeTPrime_vadd k p hf)

end Regularity

section Uniqueness

theorem qExpansion_coeff_unique' {g : ℍ → ℂ} (hcont : Continuous g) {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction 1 g) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion 1 g).coeff m :=
  UpperHalfPlane.qExpansion_coeff_unique (ContinuousMap.mk g hcont) one_pos hg hs m

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem hasSum_qCoeff [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) τ

theorem eq_of_forall_qCoeff_eq [ModularFormClass F Γ k] {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) : f = g := by
  refine DFunLike.ext f g fun τ => ?_
  have hf := hasSum_qCoeff f hΓ τ
  have hg := hasSum_qCoeff g hΓ τ
  simp only [h] at hf
  exact hf.unique hg

end Uniqueness

section QExpAction

theorem qParam_one (z : ℂ) : Periodic.qParam 1 z = exp (2 * π * I * z) := by
  simp [Periodic.qParam]

variable {p : ℕ} (hp : p ≠ 0)

include hp in
theorem natCast_ne_zero' : (p : ℂ) ≠ 0 := by exact_mod_cast hp

include hp in
theorem qParam_heckeMatrix_smul (j : ℕ) (τ : ℍ) :
    Periodic.qParam 1 ((heckeMatrix p j • τ : ℍ) : ℂ)
      = exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j := by
  rw [qParam_one, coe_heckeMatrix_smul hp, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have := natCast_ne_zero' hp
  field_simp

include hp in
theorem qParam_heckeDiagMatrix_smul (τ : ℍ) :
    Periodic.qParam 1 ((heckeDiagMatrix p • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ p := by
  rw [qParam_one, qParam_one, coe_heckeDiagMatrix_smul hp, ← Complex.exp_nat_mul]
  congr 1
  ring

include hp in
theorem exp_div_pow (τ : ℍ) : exp (2 * π * I * τ / p) ^ p = Periodic.qParam 1 τ := by
  rw [qParam_one, ← Complex.exp_nat_mul]
  congr 1
  have := natCast_ne_zero' hp
  field_simp

include hp in
theorem sum_rootOfUnity_pow (m : ℕ) :
    ∑ j ∈ Finset.range p, (exp (2 * π * I / p) ^ j) ^ m = if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp
  have hswap : ∀ j : ℕ, (exp (2 * π * I / p) ^ j) ^ m = (exp (2 * π * I / p) ^ m) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm j m]
  simp only [hswap]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).mpr h]
    simp
  · have hne : exp (2 * π * I / p) ^ m ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd m).mp h1)
    rw [geom_sum_eq hne, ← pow_mul, Nat.mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div]

theorem not_dvd_of_not_mem_range {m : ℕ} (hm : m ∉ Set.range (fun l : ℕ ↦ l * p)) : ¬ p ∣ m := by
  rintro ⟨l, rfl⟩
  exact hm ⟨l, by simp [mul_comm]⟩

variable {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
  (hbdd : IsBoundedAtImInfty f)

include hp hper hhol hbdd in
theorem hasSum_average (τ : ℍ) :
    HasSum (fun l : ℕ ↦ qCoeff f (l * p) * Periodic.qParam 1 τ ^ l)
      ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)) := by
  have hF : ∀ τ' : ℍ, HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ' ^ m) (f τ') :=
    hasSum_qExpansion one_pos hper hhol hbdd
  have h1 : HasSum (fun m ↦ ∑ j ∈ Finset.range p,
      qCoeff f m • (exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j) ^ m)
      (∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)) := by
    refine hasSum_sum fun j _ => ?_
    have := hF (heckeMatrix p j • τ)
    rwa [qParam_heckeMatrix_smul hp j τ] at this
  have h2 : (fun m ↦ ∑ j ∈ Finset.range p,
      qCoeff f m • (exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j) ^ m)
      = fun m ↦ if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0 := by
    funext m
    simp only [mul_pow, smul_eq_mul, ← Finset.mul_sum, sum_rootOfUnity_pow hp m]
    split_ifs <;> ring
  rw [h2] at h1
  have hinj : Function.Injective (fun l : ℕ ↦ l * p) := mul_left_injective₀ hp
  have h3 := (hinj.hasSum_iff (f := fun m ↦
      if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0)
    (fun m hm => by simp [not_dvd_of_not_mem_range hm])).mpr h1
  have h4 : ((fun m ↦ if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0) ∘
      fun l : ℕ ↦ l * p) = fun l ↦ (p : ℂ) * (qCoeff f (l * p) * Periodic.qParam 1 τ ^ l) := by
    funext l
    simp only [comp_apply, ite_eq_left (dvd_mul_left p l)]
    rw [mul_comm l p, pow_mul, exp_div_pow hp τ]
    ring
  rw [h4] at h3
  have h5 := h3.mul_left ((p : ℂ)⁻¹)
  simp only [← mul_assoc, inv_mul_cancel₀ (natCast_ne_zero' hp), one_mul] at h5
  exact h5

include hp hper hhol hbdd in
theorem hasSum_diag (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ if p ∣ n then (p : ℂ) ^ (k - 1) * qCoeff f (n / p) * Periodic.qParam 1 τ ^ n
        else 0)
      ((p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ)) := by
  have hD := (hasSum_qExpansion one_pos hper hhol hbdd (heckeDiagMatrix p • τ)).mul_left
    ((p : ℂ) ^ (k - 1))
  rw [qParam_heckeDiagMatrix_smul hp τ] at hD
  have hinj : Function.Injective (fun l : ℕ ↦ l * p) := mul_left_injective₀ hp
  refine (hinj.hasSum_iff (fun m hm => by simp [not_dvd_of_not_mem_range hm])).mp ?_
  convert hD using 1
  · funext l
    simp only [comp_apply, ite_eq_left (dvd_mul_left p l),
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hp), smul_eq_mul, ModularFormClass.qCoeff]
    rw [← pow_mul, mul_comm l p, mul_assoc]

include hp hper hhol hbdd in
theorem hasSum_heckeU (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ coeffHeckeU p (qCoeff f) n • Periodic.qParam 1 τ ^ n) (heckeU k p f τ) := by
  rw [heckeU_apply k hp]
  simpa only [coeffHeckeU_apply, smul_eq_mul] using hasSum_average hp hper hhol hbdd τ

include hper hhol hbdd in
theorem hasSum_heckeTPrime [Fact p.Prime] (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ coeffHeckeTPrime k p (qCoeff f) n • Periodic.qParam 1 τ ^ n)
      (heckeTPrime k p f τ) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [heckeTPrime_apply k p]
  convert (hasSum_average hp hper hhol hbdd τ).add (hasSum_diag hp hper hhol hbdd k τ) using 1
  funext n
  rw [coeffHeckeTPrime_apply, smul_eq_mul]
  split_ifs <;> ring

include hp hper hhol hbdd in
theorem qCoeff_heckeU_bare (k : ℤ) (n : ℕ) :
    qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n :=
  (qExpansion_coeff_unique' (mdifferentiable_heckeU k p hhol).continuous
    (analyticAt_cuspFunction_zero one_pos (periodic_heckeU_comp_ofComplex k p hper)
      (mdifferentiable_heckeU k p hhol) (isBoundedAtImInfty_heckeU k p hbdd))
    (hasSum_heckeU hp hper hhol hbdd k) n).symm

include hper hhol hbdd in
theorem qCoeff_heckeTPrime_bare [Fact p.Prime] (k : ℤ) (n : ℕ) :
    qCoeff (heckeTPrime k p f) n = coeffHeckeTPrime k p (qCoeff f) n :=
  (qExpansion_coeff_unique' (mdifferentiable_heckeTPrime k p hhol).continuous
    (analyticAt_cuspFunction_zero one_pos (periodic_heckeTPrime_comp_ofComplex k p hper)
      (mdifferentiable_heckeTPrime k p hhol) (isBoundedAtImInfty_heckeTPrime k p hbdd))
    (hasSum_heckeTPrime hper hhol hbdd k) n).symm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

include hp in
theorem qCoeff_heckeU_class [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (n : ℕ) : qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_heckeU_bare hp (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) k n

theorem qCoeff_heckeTPrime_class [Fact p.Prime] [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    qCoeff (heckeTPrime k p f) n = coeffHeckeTPrime k p (qCoeff f) n :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_heckeTPrime_bare (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) k n

end QExpAction

end ModularFormHeckeUQExp


namespace ModularForm

/-- The Hecke `U` operator preserves differentiability on the upper half-plane. -/
public theorem mdifferentiable_heckeU {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f)
    (k : ℤ) (p : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (heckeU k p f) :=
  ModularFormHeckeUQExp.mdifferentiable_heckeU k p hf

end ModularForm

namespace ModularFormClass

/-- Coefficients of `heckeU`: the `n`-th coefficient is the `(n*p)`-th of the original. -/
public theorem qCoeff_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (qCoeff f) n :=
  ModularFormHeckeUQExp.qCoeff_heckeU_class hp f hΓ n

end ModularFormClass

namespace ModularForm

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace S06W2

open UpperHalfPlane OnePoint

section RatCusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

theorem isCusp_ratCast_smul {c : OnePoint ℝ} (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem isBoundedAt_slash_ratCast [ModularFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) {c : OnePoint
  ℝ}
    (hc : IsCusp c Γ) : c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k
      :=
  OnePoint.IsBoundedAt.smul_iff.mp (ModularFormClass.bdd_at_cusps f (isCusp_ratCast_smul hc g))

theorem isZeroAt_slash_ratCast [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k :=
  OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f (isCusp_ratCast_smul hc g))

end RatCusps

section HeckeMatrices

def ratUpperTriangularGL (a b d : ℚ) (had : a * d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

theorem upperTriangularGL_eq_map (a b d : ℚ) (had : a * d ≠ 0) :
    upperTriangularGL a b d (by exact_mod_cast had) =
      Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (ratUpperTriangularGL a b d had) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ratUpperTriangularGL, upperTriangularGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_heckeMatrix_eq_map (p j : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeMatrix p j = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeMatrix, hp, ratUpperTriangularGL, upperTriangularGL,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_heckeDiagMatrix_eq_map (p : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeDiagMatrix p = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeDiagMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeDiagMatrix, hp, ratUpperTriangularGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

end HeckeMatrices

section Cusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

theorem isBoundedAt_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, c.IsBoundedAt (f i) k) : c.IsBoundedAt (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.const_boundedAtFilter _ (0 : ℂ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem
      hi))

theorem isZeroAt_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, c.IsZeroAt (f i) k) : c.IsZeroAt (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem
      hi))

theorem isBoundedAt_heckeU [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c
  Γ) :
    c.IsBoundedAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isBoundedAt_sum _ fun j _ => ?_
  obtain ⟨g, hg⟩ := exists_heckeMatrix_eq_map p j
  rw [hg]
  exact isBoundedAt_slash_ratCast f g hc

theorem isBoundedAt_heckeTPrime [ModularFormClass F Γ k] (f : F) (p : ℕ) [Fact p.Prime]
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsBoundedAt (heckeTPrime k p ⇑f) k := by
  rw [heckeTPrime_eq_heckeU_add]
  refine (isBoundedAt_heckeU f p hc).add ?_
  obtain ⟨g, hg⟩ := exists_heckeDiagMatrix_eq_map p
  rw [hg]
  exact isBoundedAt_slash_ratCast f g hc

theorem isZeroAt_heckeU [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isZeroAt_sum _ fun j _ => ?_
  obtain ⟨g, hg⟩ := exists_heckeMatrix_eq_map p j
  rw [hg]
  exact isZeroAt_slash_ratCast f g hc

theorem isZeroAt_heckeTPrime [CuspFormClass F Γ k] (f : F) (p : ℕ) [Fact p.Prime]
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (heckeTPrime k p ⇑f) k := by
  rw [heckeTPrime_eq_heckeU_add]
  refine (isZeroAt_heckeU f p hc).add ?_
  obtain ⟨g, hg⟩ := exists_heckeDiagMatrix_eq_map p
  rw [hg]
  exact isZeroAt_slash_ratCast f g hc

end Cusps

end ModularForm.S06W2


namespace CuspFormClass

/-- The Hecke `U` operator preserves vanishing at cusps. -/
public theorem isZeroAt_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k]
    (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsZeroAt c (ModularForm.heckeU k p ⇑f) k :=
  ModularForm.S06W2.isZeroAt_heckeU f p hc

end CuspFormClass

namespace ModularFormHeckeGammaH

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace HeckeGammaH

section

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

noncomputable def beta (c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q)
  : GL (Fin 2) ℝ :=
  ModularForm.heckeMatrix q 0 *
    (Matrix.SpecialLinearGroup.mapGL ℝ (((c.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))⁻¹) :
      GL (Fin 2) ℝ)

omit [NeZero M] in
theorem mapGL_conjL_mul_heckeMatrix (t : ↥(CongruenceSubgroup.GammaHUpper M H q)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q t :
      ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q 0 =
      ModularForm.heckeMatrix q 0 *
        (Matrix.SpecialLinearGroup.mapGL ℝ (((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))) :
          GL (Fin 2) ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hdvd : (q : ℤ) ∣ (((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin
    2) ℤ) 0 1 :=
    dvd_of_mem_GammaHUpper M H q t
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq]
  have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q t :
    ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((CongruenceSubgroup.conjUpperMat q ((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) hdvd :
        SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := rfl
  have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ ((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))
    : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := rfl
  have hcast : (((((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0
    1 / q : ℤ) : ℝ) * q =
      (((((t : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) :
        ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hdvd
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CongruenceSubgroup.conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hcast, mul_comm]

theorem sum_slash_beta_slash_eq (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ =
      f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.GammaH M H).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) :
    letI := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q, f ∣[k] beta M H
      q c) ∣[k] γ =
      ∑ c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q, f ∣[k] beta M H
        q c := by
  let := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  set g' : ↥(CongruenceSubgroup.GammaH M H) := ⟨g, hg⟩ with hg'
  have hterm : ∀ c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q,
      (f ∣[k] beta M H q c) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
        f ∣[k] beta M H q (g'⁻¹ • c) := by
    intro c
    set d := g'⁻¹ • c with hd
    have hmk : (QuotientGroup.mk (g'⁻¹ * c.out) : ↥(CongruenceSubgroup.GammaH M H) ⧸
      CongruenceSubgroup.GammaHUpper M H q) = d := by
      rw [hd]
      conv_rhs => rw [← QuotientGroup.out_eq' c]
      rw [MulAction.Quotient.smul_mk]
      rfl
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.GammaHUpper M H q) (g'⁻¹ *
      c.out)
    rw [hmk] at ht
    have hrel : (((c.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)))⁻¹ * g =
        (((t : ↥(CongruenceSubgroup.GammaHUpper M H q)) : ↥(CongruenceSubgroup.GammaH M H)) : SL(2,
          ℤ)) * (((d.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)))⁻¹ := by
      have h1 : ((d.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) =
          (g⁻¹ * ((c.out : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))) * (((t :
            ↥(CongruenceSubgroup.GammaHUpper M H q)) : ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ))
              := by
        have := congrArg (fun x : ↥(CongruenceSubgroup.GammaH M H) => (x : SL(2, ℤ))) ht
        simpa using this
      rw [h1]; group
    rw [← SlashAction.slash_mul]
    have hb : beta M H q c * (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q t :
          ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          beta M H q d := by
      simp only [beta]
      rw [mul_assoc, ← map_mul, hrel, map_mul, ← mul_assoc, ← mapGL_conjL_mul_heckeMatrix,
        mul_assoc]
    rw [hb, SlashAction.slash_mul, hf _ (Subgroup.mem_map_of_mem _ (CongruenceSubgroup.conjL M H q
      t).2)]
  classical
  have hsum : ∀ (s : Finset (↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H
    q)) (F : (↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q) → ℍ → ℂ)
      (A : GL (Fin 2) ℝ), (∑ c ∈ s, F c) ∣[k] A = ∑ c ∈ s, (F c) ∣[k] A := by
    intro s F A
    induction s using Finset.induction_on with
    | empty => simp [SlashAction.zero_slash]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  rw [hsum]
  simp_rw [hterm]
  exact Fintype.sum_bijective (g'⁻¹ • ·) (MulAction.bijective g'⁻¹) _ _ (fun c => rfl)

end

end HeckeGammaH

namespace HeckeGammaH

section Affine

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]

def transl (n : ℤ) : ↥(CongruenceSubgroup.GammaH M H) :=
  ⟨ModularGroup.T ^ n, by
    rw [mem_GammaH_iff M]
    have h0 : ModularGroup.T ^ n ∈ Gamma0 M := by
      rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp
    refine ⟨h0, ?_⟩
    have : gamma0Units M ⟨ModularGroup.T ^ n, h0⟩ = 1 := by
      ext; rw [val_gamma0Units]
      change (((ModularGroup.T ^ n) 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
      rw [ModularGroup.coe_T_zpow]; simp
    rw [this]; exact one_mem H⟩

omit [NeZero M] in
@[scoped simp] theorem coe_transl (n : ℤ) : ((transl M H n : ↥(CongruenceSubgroup.GammaH M H)) :
  SL(2, ℤ)) = ModularGroup.T ^ n := rfl

theorem exists_add_neg_eq_mul (j : Fin q) : ∃ e : ℕ, (j : ℕ) + ((-j : Fin q) : ℕ) = e * q := by
  have h : ((j : ℕ) + ((-j : Fin q) : ℕ)) % q = 0 := by
    have := Fin.val_add j (-j)
    rw [add_neg_cancel, Fin.val_zero] at this
    exact this.symm
  exact ⟨((j : ℕ) + ((-j : Fin q) : ℕ)) / q, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm⟩

theorem heckeMatrix_zero_mul_mapGL_T_zpow_neg (j : Fin q) (e : ℕ) (he : (j : ℕ) + ((-j : Fin q) : ℕ)
  = e * q) :
    ModularForm.heckeMatrix q 0 * (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ ((j : ℕ) :
      ℤ))⁻¹) : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
        ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
  have hq : q ≠ 0 := NeZero.ne q
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ModularForm.val_heckeMatrix hq, ModularForm.val_heckeMatrix hq]
  have e1 : ∀ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ n)⁻¹) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (-n : ℝ); 0, 1] := by
    intro n
    rw [← zpow_neg, show ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (-n))) : GL (Fin 2)
      ℝ) =
      ((ModularGroup.T ^ (-n) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) from rfl,
      ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [e1, e1]
  have he' : ((j : ℕ) : ℝ) + (((-j : Fin q) : ℕ) : ℝ) = (e : ℝ) * (q : ℝ) := by exact_mod_cast he
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linarith [he']

omit [NeZero M] in
theorem bijective_transl (hqM : q ∣ M) :
    Function.Bijective (fun j : Fin q => (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ)) :
      ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q)) := by
  have hq : q ≠ 0 := NeZero.ne q
  constructor
  · intro i j hij
    rw [QuotientGroup.eq] at hij
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl, coe_transl, ←
      zpow_neg, ← zpow_add,
      mem_Gamma0Upper, ModularGroup.coe_T_zpow] at hij
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero] at hij
    apply Fin.ext
    have h1 : ((j : ℕ) : ZMod q) = ((i : ℕ) : ZMod q) := by
      have : ((-(i : ℕ) + (j : ℕ) : ℤ) : ZMod q) = 0 := by exact_mod_cast hij
      push_cast at this
      linear_combination this
    have := (ZMod.natCast_eq_natCast_iff' (j : ℕ) (i : ℕ) q).mp h1
    rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt i.2] at this
    exact this.symm
  · intro c
    induction c using QuotientGroup.induction_on with
    | H γ =>
    obtain ⟨h0, -⟩ := (mem_GammaH_iff M).mp γ.2
    have hc : ((((γ : SL(2, ℤ)) 1 0 : ℤ)) : ZMod q) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (Int.natCast_dvd_natCast.mpr hqM).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        (Gamma0_mem.mp h0))
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
    rw [Matrix.det_fin_two] at hdet
    have had : ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) * ((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod q) = 1 :=
      by
      have := congrArg (fun z : ℤ => (z : ZMod q)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at this
      exact this
    set jz : ZMod q := ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q)
      with hjz
    refine ⟨⟨jz.val, ZMod.val_lt jz⟩, ?_⟩
    symm
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_transl,
      mem_Gamma0Upper]
    have hentry : ((γ : SL(2, ℤ))⁻¹ * ModularGroup.T ^ (((jz.val : ℕ) : ℤ)) : SL(2, ℤ)) 0 1 =
        ((γ : SL(2, ℤ)) 1 1 : ℤ) * ((jz.val : ℕ) : ℤ) - ((γ : SL(2, ℤ)) 0 1 : ℤ) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        ModularGroup.coe_T_zpow,
        Matrix.adjugate_fin_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hentry]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, hjz]
    linear_combination ((((γ : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) * had

theorem sum_slash_beta_eq_heckeU (hqM : q ∣ M) (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ), f ∣[k] γ =
      f) :
    letI := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(CongruenceSubgroup.GammaH M H) ⧸ CongruenceSubgroup.GammaHUpper M H q, f ∣[k] beta M H
      q c) = ModularForm.heckeU k q f := by
  let := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  rw [← Fintype.sum_bijective _ (bijective_transl M H q hqM) (fun j => f ∣[k] beta M H q
      (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ)))) _ (fun _ => rfl)]
  have hterm : ∀ j : Fin q, f ∣[k] beta M H q (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
      f ∣[k] ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
    intro j
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.GammaHUpper M H q) (transl M H
      ((j : ℕ) : ℤ))
    obtain ⟨e, he⟩ := exists_add_neg_eq_mul q j
    have hb : beta M H q (QuotientGroup.mk (transl M H ((j : ℕ) : ℤ))) =
        (Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q k⁻¹ :
          ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) *
          ModularForm.heckeMatrix q ((-j : Fin q) : ℕ) := by
      simp only [beta]
      rw [hk, Subgroup.coe_mul, mul_inv_rev, map_mul, ← mul_assoc,
        show (((k : ↥(CongruenceSubgroup.GammaHUpper M H q)) : ↥(CongruenceSubgroup.GammaH M H)) :
          SL(2, ℤ))⁻¹ =
          (((k⁻¹ : ↥(CongruenceSubgroup.GammaHUpper M H q)) : ↥(CongruenceSubgroup.GammaH M H)) :
            SL(2, ℤ)) from rfl,
        ← mapGL_conjL_mul_heckeMatrix, mul_assoc, coe_transl,
        heckeMatrix_zero_mul_mapGL_T_zpow_neg q j e he, ← mul_assoc]
    have hmem1 : (Matrix.SpecialLinearGroup.mapGL ℝ ((CongruenceSubgroup.conjL M H q k⁻¹ :
      ↥(CongruenceSubgroup.GammaH M H)) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) ∈ (CongruenceSubgroup.GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
      Subgroup.mem_map_of_mem _ (CongruenceSubgroup.conjL M H q k⁻¹).2
    have hmem2 : (Matrix.SpecialLinearGroup.mapGL ℝ ((ModularGroup.T ^ (e : ℤ))⁻¹) : GL (Fin 2) ℝ) ∈
        (CongruenceSubgroup.GammaH M H).map (Matrix.SpecialLinearGroup.mapGL ℝ) := by
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← zpow_neg]
      exact (transl M H (-(e : ℤ))).2
    rw [hb, SlashAction.slash_mul, SlashAction.slash_mul, hf _ hmem1,
      hf _ hmem2]
  simp_rw [hterm]
  rw [ModularForm.heckeU_def, ← Fin.sum_univ_eq_sum_range (fun i => f ∣[k] ModularForm.heckeMatrix q
    i) q]
  exact Fintype.sum_equiv (Equiv.neg (Fin q)) _ _ (fun j => rfl)

end Affine

end HeckeGammaH

end ModularFormHeckeGammaH

namespace ModularForm

/-- For a prime dividing the level, `heckeU` is invariant under slashing by
elements of the intermediate congruence subgroup. -/
public theorem heckeU_slash_eq_self_of_mem_GammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    (heckeU k q f) ∣[k] γ = heckeU k q f := by
  have : NeZero q := ⟨hq.ne_zero⟩
  let := (CongruenceSubgroup.GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  rw [← ModularFormHeckeGammaH.HeckeGammaH.sum_slash_beta_eq_heckeU M H q hqM k hf]
  exact ModularFormHeckeGammaH.HeckeGammaH.sum_slash_beta_slash_eq M H q k hf γ hγ

end ModularForm

namespace CuspForm

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

/-- Stability of cusp forms for `GammaH` under the `U` operator at a bad prime:
invariance, differentiability, and vanishing at cusps of `heckeU`. -/
public def StableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (q : ℕ) : Prop :=
∀ f : CuspForm (CongruenceSubgroup.GammaH M H) k,
    (∀ γ ∈ (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
      (ModularForm.heckeU k q ⇑f) ∣[k] γ = ModularForm.heckeU k q ⇑f) ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k q
      ⇑f) ∧
    ∀ c : OnePoint ℝ, IsCusp c (CongruenceSubgroup.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      OnePoint.IsZeroAt c (ModularForm.heckeU k q ⇑f) k

noncomputable def heckeULinHOf (k : ℤ) {q : ℕ} (hU : StableU M H k q) :
    CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.GammaH M H) k
      where
  toFun f :=
    { toFun := ModularForm.heckeU k q ⇑f
      slash_action_eq' := fun γ hγ => (hU f).1 γ hγ
      holo' := (hU f).2.1
      zero_at_cusps' := fun hc => (hU f).2.2 _ hc }
  map_add' f g := DFunLike.coe_injective <|
    show ModularForm.heckeU k q ⇑(f + g) = ModularForm.heckeU k q ⇑f + ModularForm.heckeU k q ⇑g by
      rw [FunLike.coe_add, ModularForm.heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show ModularForm.heckeU k q ⇑(c • f) = c • ModularForm.heckeU k q ⇑f by
      rw [FunLike.coe_smul, ModularForm.heckeU_smul]

end CuspForm

namespace CuspForm

/-- Cusp forms for `GammaH` are stable under `heckeU` at a prime dividing the level. -/
public theorem stableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) : StableU M H k q := by
  intro f
  exact ⟨fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H k hq hqM
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k q,
    fun c hc => CuspFormClass.isZeroAt_heckeU f q hc⟩

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

/-- The Hecke operator `U_q` on cusp forms for `GammaH M H`, for a prime `q` dividing the level
`M`: the linear map `f ↦ heckeU k q f`, built by `heckeULinHOf` from `stableU`. It takes the
primality and divisibility hypotheses, so it is not defined at other indices. -/
noncomputable def heckeULinH (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.GammaH M H) k :=
  heckeULinHOf k (stableU M H k hq hqM)

theorem heckeULinH_eq (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hU : StableU M H k q) :
    (heckeULinH k hq hqM : CuspForm (CongruenceSubgroup.GammaH M H) k →ₗ[ℂ] _) =
      heckeULinHOf k hU :=
  rfl

theorem coe_heckeULinH_apply (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    ⇑(heckeULinH k hq hqM f) = ModularForm.heckeU k q ⇑f :=
  rfl

end CuspForm

namespace CuspForm

private theorem one_mem_strictPeriods_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.GammaH M H : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.GammaH M H :=
    CongruenceSubgroup.gamma1_le_gammaH M H
      (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

private theorem eq_of_forall_qCoeff_eq (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (F G : CuspForm (CongruenceSubgroup.GammaH M H) k)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff F n = ModularFormClass.qCoeff G n) :
    F = G := by
  have hΓ := one_mem_strictPeriods_GammaH M H
  have : Fact (IsCusp OnePoint.infty
      ((CongruenceSubgroup.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have h1 : UpperHalfPlane.qExpansion 1 (⇑(F - G)) = 0 := by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos hΓ F G]
    ext n
    have hh := h n
    simp only [ModularFormClass.qCoeff] at hh
    simp [hh]
  have h2 : (⇑(F - G) : UpperHalfPlane → ℂ) = 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex (F - G) hΓ)
      (ModularFormClass.holo (F - G)) (ModularFormClass.bdd_at_infty (F - G))).mp h1
  have h3 : F - G = 0 := DFunLike.ext' (by rw [h2]; rfl)
  exact sub_eq_zero.mp h3

public theorem qCoeff_heckeULinH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (heckeULinH k hq hqM f) n = ModularFormClass.qCoeff f (n * q) := by
  have hcoe : ModularFormClass.qCoeff (⇑(heckeULinH k hq hqM f)) n =
      ModularFormClass.qCoeff (ModularForm.heckeU k q ⇑f) n := by
    rw [coe_heckeULinH_apply k hq hqM f]
  rw [hcoe, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods_GammaH M H) hq.ne_zero n,
    ModularForm.coeffHeckeU_apply]

/-- The `U` operators at two primes dividing the level commute on cusp forms
for the intermediate congruence subgroup. -/
public theorem heckeULinH_comm
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k) :
    heckeULinH k hq hqM (heckeULinH k hq' hq'M f) =
      heckeULinH k hq' hq'M (heckeULinH k hq hqM f) := by
  apply eq_of_forall_qCoeff_eq M H
  intro n
  rw [qCoeff_heckeULinH M H k hq hqM, qCoeff_heckeULinH M H k hq' hq'M,
    qCoeff_heckeULinH M H k hq' hq'M, qCoeff_heckeULinH M H k hq hqM, mul_right_comm]

end CuspForm
