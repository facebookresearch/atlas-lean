/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import PhyslibExt.CondensedMatter.Elasticity.StressStrain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Energy-dual lamina rotation

Rotation of an orthotropic plane-stress lamina between global and material axes in engineering
components: dual strain and stress maps and the stiffness congruence.

## i. Overview

Strains are written `(ε_xx, ε_yy, γ_xy)` with the existing engineering shear `γ_xy = 2 ε_xy`
(`Elasticity.engineeringShear`), stresses `(σ_xx, σ_yy, τ_xy)`. For material axes at the angle
`θ` from the global axes, the engineering-strain map `T_e θ` and the stress map `T_s θ` both go
GLOBAL-to-MATERIAL; they are different matrices, dual to each other: `T_sᵀ T_e = 1`, so
`T_s = T_e⁻ᵀ`. Both act on Voigt components as the tensor rotation
`Elasticity.rotatedStress2 σ θ = R θ σ (R θ)ᵀ`. With the material law `σ₁₂ = Q ε₁₂` the global
stiffness is the congruence `Q_global = T_eᵀ Q T_e`, the only matrix that reproduces the material
law; work and strain energy are frame independent, and positive definiteness transfers by
congruence. The inverse-congruence formula `A⁻ᵀ Q A⁻¹` holds for the MATERIAL-to-GLOBAL map
`A = T_e(-θ)`; applied to the GLOBAL-to-MATERIAL map it gives the lamina at `-θ`.

Model inputs (hypotheses of the module):

* plane stress, linear elastic orthotropic lamina; `Q` is the material-axes stiffness in the
  energy-conjugate engineering components, symmetric positive definite where stated;
* the material axes are the global axes turned by the proper rotation `θ`, the convention of
  `Elasticity.rotationMatrix2` and `Elasticity.rotatedStress2`;
* tensors are symmetric where Voigt components are taken.

Non-goals: laminate assembly, homogenization, failure or damage laws, transverse shear, and any
empirical adequacy or system safety claim.

## ii. Key results

- `stressVoigt_dotProduct_strainVoigt`, `strainVoigt_inPlane_two` : the engineering pairing is
  the tensor contraction `tr (σ ε)`, and the shear entry is the existing engineering shear.
- `stressMap_mulVec_stressVoigt`, `strainMap_mulVec_strainVoigt` : the two GLOBAL-to-MATERIAL
  maps act on Voigt components as the tensor rotation.
- `stressMap_transpose_mul_strainMap`, `stressMap_eq_transpose_inv`,
  `stressMap_mulVec_dotProduct_strainMap_mulVec` : `T_sᵀ T_e = 1`, `T_s = T_e⁻ᵀ` and work
  invariance.
- `stressMap_mulVec_eq_iff_eq_globalStiffness`, `dotProduct_globalStiffness_mulVec`,
  `globalStiffness_posDef` : `Q_global = T_eᵀ Q T_e` is the unique stiffness consistent with the
  material law, carries the same strain energy, and is positive definite with `Q`.
- `strainMap_inv`, `globalStiffness_eq_inv_congr`, `inv_congr_strainMap` : the inverse-congruence
  formula and the convention it applies to.

## iii. Table of contents

- A. Engineering components and the shear convention
- B. The two GLOBAL-to-MATERIAL maps
- C. Work duality
- D. Stiffness congruence
- E. The opposite MATERIAL-to-GLOBAL convention

## iv. References

- R. M. Jones, *Mechanics of Composite Materials*, 2nd edition, 1999, chapter 2 (stress and
  strain transformations of a lamina; the Reuter matrix; transformed reduced stiffnesses).
- I. M. Daniel and O. Ishai, *Engineering Mechanics of Composite Materials*, 2nd edition, 2006
  (transformation of stress, strain and stiffness of a lamina).
-/

@[expose] public section

open scoped Matrix

namespace Elasticity.LaminateModels

/-! ## A. Engineering components and the shear convention -/

/-- Stress components `(σ_xx, σ_yy, τ_xy)` of a plane stress tensor. -/
def stressVoigt (σ : Matrix (Fin 2) (Fin 2) ℝ) : Fin 3 → ℝ :=
  ![σ 0 0, σ 1 1, σ 0 1]

/-- Engineering strain components `(ε_xx, ε_yy, γ_xy)` of a plane strain tensor, with the
engineering shear `γ_xy = 2 ε_xy`. -/
noncomputable def strainVoigt (ε : Matrix (Fin 2) (Fin 2) ℝ) : Fin 3 → ℝ :=
  ![ε 0 0, ε 1 1, 2 * ε 0 1]

/-- The in-plane block (first two axes) of a three-dimensional tensor. -/
def inPlane (ε : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ε (Fin.castSucc i) (Fin.castSucc j)

/-- The shear component of the engineering strain is the existing engineering shear of the
in-plane block. -/
lemma strainVoigt_inPlane_two (ε : Matrix (Fin 3) (Fin 3) ℝ) :
    strainVoigt (inPlane ε) 2 = engineeringShear ε := by
  simp only [strainVoigt, inPlane, engineeringShear, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.castSucc_zero']
  rfl

/-- Energy conjugacy: for symmetric `σ` and `ε` the engineering pairing
`σ_xx ε_xx + σ_yy ε_yy + τ_xy γ_xy` is the tensor contraction `tr (σ ε)`. -/
lemma stressVoigt_dotProduct_strainVoigt {σ ε : Matrix (Fin 2) (Fin 2) ℝ} (hσ : σᵀ = σ)
    (hε : εᵀ = ε) : stressVoigt σ ⬝ᵥ strainVoigt ε = (σ * ε).trace := by
  have hσ10 : σ 1 0 = σ 0 1 := by
    have h := congr_fun (congr_fun hσ 0) 1
    rwa [Matrix.transpose_apply] at h
  have hε10 : ε 1 0 = ε 0 1 := by
    have h := congr_fun (congr_fun hε 0) 1
    rwa [Matrix.transpose_apply] at h
  simp only [stressVoigt, strainVoigt, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.mul_apply,
    hσ10, hε10]
  ring

/-! ## B. The two GLOBAL-to-MATERIAL maps -/

/-- Engineering-strain map GLOBAL-to-MATERIAL for material axes at the angle `θ` from the global
axes: `(ε₁₁, ε₂₂, γ₁₂) = T_e θ (ε_xx, ε_yy, γ_xy)`. -/
noncomputable def strainMap (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ ^ 2, Real.sin θ ^ 2, Real.cos θ * Real.sin θ;
    Real.sin θ ^ 2, Real.cos θ ^ 2, -(Real.cos θ * Real.sin θ);
    -(2 * Real.cos θ * Real.sin θ), 2 * Real.cos θ * Real.sin θ,
      Real.cos θ ^ 2 - Real.sin θ ^ 2]

/-- Stress map GLOBAL-to-MATERIAL: `(σ₁₁, σ₂₂, τ₁₂) = T_s θ (σ_xx, σ_yy, τ_xy)`. -/
noncomputable def stressMap (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ ^ 2, Real.sin θ ^ 2, 2 * Real.cos θ * Real.sin θ;
    Real.sin θ ^ 2, Real.cos θ ^ 2, -(2 * Real.cos θ * Real.sin θ);
    -(Real.cos θ * Real.sin θ), Real.cos θ * Real.sin θ, Real.cos θ ^ 2 - Real.sin θ ^ 2]

/-- The stress map gives material components: for a symmetric plane stress `σ`,
`T_s θ (σ_xx, σ_yy, τ_xy)` are the components of the rotated stress `rotatedStress2 σ θ`. -/
lemma stressMap_mulVec_stressVoigt (θ : ℝ) {σ : Matrix (Fin 2) (Fin 2) ℝ} (hσ : σᵀ = σ) :
    stressMap θ *ᵥ stressVoigt σ = stressVoigt (rotatedStress2 σ θ) := by
  have hσ10 : σ 1 0 = σ 0 1 := by
    have h := congr_fun (congr_fun hσ 0) 1
    rwa [Matrix.transpose_apply] at h
  ext i
  fin_cases i <;>
    simp [stressMap, stressVoigt, rotatedStress2, rotationMatrix2, Matrix.mulVec, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, hσ10] <;>
    ring

/-- The strain map gives material engineering components: for a symmetric plane strain `ε`,
`T_e θ (ε_xx, ε_yy, γ_xy)` are the engineering components of the rotated strain
`R θ ε (R θ)ᵀ`. -/
lemma strainMap_mulVec_strainVoigt (θ : ℝ) {ε : Matrix (Fin 2) (Fin 2) ℝ} (hε : εᵀ = ε) :
    strainMap θ *ᵥ strainVoigt ε =
      strainVoigt (rotationMatrix2 θ * ε * (rotationMatrix2 θ)ᵀ) := by
  have hε10 : ε 1 0 = ε 0 1 := by
    have h := congr_fun (congr_fun hε 0) 1
    rwa [Matrix.transpose_apply] at h
  ext i
  fin_cases i <;>
    simp [strainMap, strainVoigt, rotationMatrix2, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, hε10] <;>
    ring

/-! ## C. Work duality -/

/-- Work duality of the two maps: `T_sᵀ T_e = 1`. -/
lemma stressMap_transpose_mul_strainMap (θ : ℝ) : (stressMap θ)ᵀ * strainMap θ = 1 := by
  have h := Real.cos_sq_add_sin_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stressMap, strainMap, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two,
      Matrix.transpose_apply] <;>
    try ring1
  all_goals linear_combination (Real.cos θ ^ 2 + Real.sin θ ^ 2 + 1) * h

/-- The stress map is the inverse transpose of the strain map: `T_s = T_e⁻ᵀ`. -/
lemma stressMap_eq_transpose_inv (θ : ℝ) : stressMap θ = ((strainMap θ)⁻¹)ᵀ := by
  have h : (strainMap θ)⁻¹ = (stressMap θ)ᵀ :=
    Matrix.inv_eq_left_inv (stressMap_transpose_mul_strainMap θ)
  rw [h, Matrix.transpose_transpose]

/-- Work invariance: the work of a global stress `s` on a global engineering strain `e` equals
the work of their material components, `(T_s s) ⬝ (T_e e) = s ⬝ e`. -/
lemma stressMap_mulVec_dotProduct_strainMap_mulVec (θ : ℝ) (s e : Fin 3 → ℝ) :
    (stressMap θ *ᵥ s) ⬝ᵥ (strainMap θ *ᵥ e) = s ⬝ᵥ e := by
  have hTe : (strainMap θ)ᵀ * stressMap θ = 1 := by
    have h1 := congrArg Matrix.transpose (stressMap_transpose_mul_strainMap θ)
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h1
    exact h1
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hTe,
    Matrix.one_mulVec]

/-! ## D. Stiffness congruence -/

/-- Stiffness of an orthotropic lamina in material axes, in engineering components:
`σ₁₁ = Q₁₁ ε₁₁ + Q₁₂ ε₂₂`, `σ₂₂ = Q₁₂ ε₁₁ + Q₂₂ ε₂₂`, `τ₁₂ = Q₆₆ γ₁₂`. -/
def orthotropicStiffness (Q₁₁ Q₁₂ Q₂₂ Q₆₆ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Q₁₁, Q₁₂, 0; Q₁₂, Q₂₂, 0; 0, 0, Q₆₆]

/-- Global stiffness of the lamina whose material axes are at `θ`: `Q_global = T_eᵀ Q T_e`. -/
noncomputable def globalStiffness (Q : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (strainMap θ)ᵀ * Q * strainMap θ

/-- `Q_global = T_eᵀ Q T_e` is the only global stiffness consistent with the material law: a
matrix `Q_g` satisfies `T_s (Q_g e) = Q (T_e e)` for every global engineering strain `e` exactly
when `Q_g = T_eᵀ Q T_e`. -/
lemma stressMap_mulVec_eq_iff_eq_globalStiffness (Q Qg : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ) :
    (∀ e : Fin 3 → ℝ, stressMap θ *ᵥ (Qg *ᵥ e) = Q *ᵥ (strainMap θ *ᵥ e)) ↔
      Qg = globalStiffness Q θ := by
  have hcs := Real.cos_sq_add_sin_sq θ
  have hTe : (strainMap θ)ᵀ * stressMap θ = 1 := by
    have h1 := congrArg Matrix.transpose (stressMap_transpose_mul_strainMap θ)
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h1
    exact h1
  have h3 : stressMap θ * (strainMap θ)ᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stressMap, strainMap, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.cons_val_two, Matrix.transpose_apply] <;>
      try ring1
    all_goals linear_combination (Real.cos θ ^ 2 + Real.sin θ ^ 2 + 1) * hcs
  constructor
  · intro hQ
    rw [Matrix.ext_iff_mulVec]
    intro e
    have he := congrArg (fun v => (strainMap θ)ᵀ *ᵥ v) (hQ e)
    simp only [Matrix.mulVec_mulVec, ← mul_assoc] at he
    rw [hTe, one_mul] at he
    exact he
  · intro hQg e
    rw [hQg]
    change stressMap θ *ᵥ ((((strainMap θ)ᵀ * Q * strainMap θ)) *ᵥ e) =
      Q *ᵥ (strainMap θ *ᵥ e)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3,
      Matrix.one_mulVec]

/-- Strain-energy invariance: `eᵀ Q_global e = (T_e e)ᵀ Q (T_e e)`. -/
lemma dotProduct_globalStiffness_mulVec (Q : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ)
    (e : Fin 3 → ℝ) :
    e ⬝ᵥ (globalStiffness Q θ *ᵥ e) = (strainMap θ *ᵥ e) ⬝ᵥ (Q *ᵥ (strainMap θ *ᵥ e)) := by
  change e ⬝ᵥ ((((strainMap θ)ᵀ * Q * strainMap θ)) *ᵥ e) =
    (strainMap θ *ᵥ e) ⬝ᵥ (Q *ᵥ (strainMap θ *ᵥ e))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- Positive-definiteness transfer by congruence: a symmetric positive definite material
stiffness gives a symmetric positive definite global stiffness. -/
lemma globalStiffness_posDef {Q : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Q.PosDef) (θ : ℝ) :
    (globalStiffness Q θ).PosDef := by
  have hA : Function.Injective (strainMap θ).mulVec := by
    intro x y hxy
    have h1 := congrArg (fun v => (stressMap θ)ᵀ *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, stressMap_transpose_mul_strainMap,
      Matrix.one_mulVec] at h1
    exact h1
  have h := hQ.conjTranspose_mul_mul_same hA
  simpa [globalStiffness, Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-! ## E. The opposite MATERIAL-to-GLOBAL convention -/

/-- The MATERIAL-to-GLOBAL engineering-strain map is the rotation by `-θ`:
`T_e(θ)⁻¹ = T_e(-θ)`. -/
lemma strainMap_inv (θ : ℝ) : (strainMap θ)⁻¹ = strainMap (-θ) := by
  have hinv : (strainMap θ)⁻¹ = (stressMap θ)ᵀ :=
    Matrix.inv_eq_left_inv (stressMap_transpose_mul_strainMap θ)
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stressMap, strainMap, Matrix.transpose_apply, Matrix.cons_val_two, Real.cos_neg,
      Real.sin_neg]

/-- The inverse-congruence formula holds for the MATERIAL-to-GLOBAL map `A = T_e(-θ)`:
`Q_global = A⁻ᵀ Q A⁻¹`. -/
lemma globalStiffness_eq_inv_congr (Q : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ) :
    globalStiffness Q θ = ((strainMap (-θ))⁻¹)ᵀ * Q * (strainMap (-θ))⁻¹ := by
  have h : (strainMap (-θ))⁻¹ = strainMap θ := by
    rw [strainMap_inv, neg_neg]
  rw [h, globalStiffness]

/-- Applied to the GLOBAL-to-MATERIAL map instead, the inverse-congruence formula gives the
global stiffness of the lamina at `-θ`. -/
lemma inv_congr_strainMap (Q : Matrix (Fin 3) (Fin 3) ℝ) (θ : ℝ) :
    ((strainMap θ)⁻¹)ᵀ * Q * (strainMap θ)⁻¹ = globalStiffness Q (-θ) := by
  rw [strainMap_inv, globalStiffness]

end Elasticity.LaminateModels

end
