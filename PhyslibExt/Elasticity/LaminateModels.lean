/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PhyslibExt.CondensedMatter.Elasticity.StressStrain
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Energy-dual lamina rotation and finite laminate stiffness

Rotation of an orthotropic plane-stress lamina between global and material axes in engineering
components: dual strain and stress maps and the stiffness congruence; and the extensional,
coupling and bending stiffnesses of a finite stack of such plies.

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

A laminate stacks `n` plies: ply `i` occupies `[z i, z (i + 1)]` between consecutive interfaces
and has the reduced stiffness `Q̄ i` in global axes (for an angle ply, `globalStiffness`). Under
the Kirchhoff kinematics the strain at height `s` is `ε⁰ + s κ` (midplane strain `ε⁰`, curvature
`κ`), so the stress in ply `i` is `Q̄ i (ε⁰ + s κ)`. Integrating the stress and its moment
through each ply gives the resultants `N = A ε⁰ + B κ` and `M = B ε⁰ + D κ`, with
`A = ∑ Q̄ i (z (i + 1) - z i)`, `B = ∑ Q̄ i (z (i + 1)² - z i²) / 2` and
`D = ∑ Q̄ i (z (i + 1)³ - z i³) / 3`. The energy of the block stiffness `[[A, B], [B, D]]` is the
sum over plies of `h (ε⁰ + z̄ κ)ᵀ Q̄ (ε⁰ + z̄ κ) + h³ κᵀ Q̄ κ / 12` (ply thickness `h`, ply
midplane `z̄`), so at least one ply, strictly increasing interfaces and positive definite ply
stiffnesses make it positive definite. A reflected stack (interfaces and ply stiffnesses mirrored
about the reference plane) has `B = 0`; a balanced `±θ` pair that is not reflected can have
`B ≠ 0`.

Model inputs (hypotheses of the module):

* plane stress, linear elastic orthotropic lamina; `Q` is the material-axes stiffness in the
  energy-conjugate engineering components, symmetric positive definite where stated;
* the material axes are the global axes turned by the proper rotation `θ`, the convention of
  `Elasticity.rotationMatrix2` and `Elasticity.rotatedStress2`;
* tensors are symmetric where Voigt components are taken;
* laminate: perfectly bonded plies with the Kirchhoff strain `ε⁰ + s κ`, heights measured from the
  reference plane, interfaces listed bottom to top; positivity of thicknesses and stiffnesses is
  assumed only where stated.

Non-goals: homogenization beyond the stated through-thickness integrals, thermal or hygral loads,
failure or damage laws, transverse shear, and any empirical adequacy or system safety claim.

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
- `forceResultant_eq`, `momentResultant_eq` : integrating the ply stresses gives
  `N = A ε⁰ + B κ` and `M = B ε⁰ + D κ`.
- `abdMatrix_energy_eq`, `abdMatrix_posDef`, `abdMatrix_energy_pos` : the ply decomposition of the
  block energy, and positive definiteness of `[[A, B], [B, D]]`.
- `couplingStiffness_eq_zero_of_isReflectedStack` : a reflected stack has no extension-bending
  coupling.

## iii. Table of contents

- A. Engineering components and the shear convention
- B. The two GLOBAL-to-MATERIAL maps
- C. Work duality
- D. Stiffness congruence
- E. The opposite MATERIAL-to-GLOBAL convention
- F. Ply geometry and the laminate stiffnesses
- G. Through-thickness integration: the resultants
- H. Block energy and positive definiteness
- I. Reflected stacks

## iv. References

- R. M. Jones, *Mechanics of Composite Materials*, 2nd edition, 1999, chapter 2 (stress and
  strain transformations of a lamina; the Reuter matrix; transformed reduced stiffnesses) and
  chapter 4 (classical lamination theory; the `A`, `B`, `D` stiffnesses; symmetric and
  antisymmetric angle-ply laminates).
- I. M. Daniel and O. Ishai, *Engineering Mechanics of Composite Materials*, 2nd edition, 2006
  (transformation of stress, strain and stiffness of a lamina; laminate force and moment
  resultants and stiffness matrices).
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

/-! ## F. Ply geometry and the laminate stiffnesses -/

variable {n : ℕ}

/-- Thickness `h i = z (i + 1) - z i` of ply `i` for the interfaces `z`. -/
def plyThickness (z : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  z i.succ - z i.castSucc

/-- Midplane height `z̄ i = (z i + z (i + 1)) / 2` of ply `i`. -/
noncomputable def plyMidplane (z : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  (z i.castSucc + z i.succ) / 2

/-- Extensional stiffness `A = ∑ Q̄ i (z (i + 1) - z i)`. -/
def extensionalStiffness (z : Fin (n + 1) → ℝ) (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ i, (z i.succ - z i.castSucc) • Q i

/-- Coupling stiffness `B = ∑ Q̄ i (z (i + 1)² - z i²) / 2`. -/
noncomputable def couplingStiffness (z : Fin (n + 1) → ℝ)
    (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ i, ((z i.succ ^ 2 - z i.castSucc ^ 2) / 2) • Q i

/-- Bending stiffness `D = ∑ Q̄ i (z (i + 1)³ - z i³) / 3`. -/
noncomputable def bendingStiffness (z : Fin (n + 1) → ℝ)
    (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ i, ((z i.succ ^ 3 - z i.castSucc ^ 3) / 3) • Q i

/-- The 6 × 6 laminate stiffness `[[A, B], [B, D]]`, acting on `(ε⁰, κ)`. -/
noncomputable def abdMatrix (z : Fin (n + 1) → ℝ) (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (extensionalStiffness z Q) (couplingStiffness z Q) (couplingStiffness z Q)
    (bendingStiffness z Q)

/-- A reflected stack: interfaces symmetric about the midplane, `z (n - k) = -z k`, and each ply
with the stiffness of its mirror ply, `Q̄ (n - 1 - i) = Q̄ i`. -/
def IsReflectedStack (z : Fin (n + 1) → ℝ) (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∀ k, z k.rev = -z k) ∧ ∀ i, Q i.rev = Q i

/-! ## G. Through-thickness integration: the resultants -/

/-- In-plane stress at height `s` in a ply of stiffness `Q`: `σ = Q (ε⁰ + s κ)`. -/
def plyStress (Q : Matrix (Fin 3) (Fin 3) ℝ) (ε κ : Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ :=
  Q *ᵥ (ε + s • κ)

/-- Force resultant `N = ∑ ∫_{z i}^{z (i + 1)} σ ds`. -/
noncomputable def forceResultant (z : Fin (n + 1) → ℝ) (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ)
    (ε κ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∑ i, ∫ s in z i.castSucc..z i.succ, plyStress (Q i) ε κ s

/-- Moment resultant `M = ∑ ∫_{z i}^{z (i + 1)} s σ ds`. -/
noncomputable def momentResultant (z : Fin (n + 1) → ℝ) (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ)
    (ε κ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∑ i, ∫ s in z i.castSucc..z i.succ, s • plyStress (Q i) ε κ s

/-- Integrating the ply stresses gives the force resultant `N = A ε⁰ + B κ`. -/
lemma forceResultant_eq (z : Fin (n + 1) → ℝ) (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ)
    (ε κ : Fin 3 → ℝ) :
    forceResultant z Q ε κ = extensionalStiffness z Q *ᵥ ε + couplingStiffness z Q *ᵥ κ := by
  have hply : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ),
      (∫ s in a..b, plyStress M ε κ s)
        = (b - a) • (M *ᵥ ε) + ((b ^ 2 - a ^ 2) / 2) • (M *ᵥ κ) := by
    intro M a b
    have hstress : ∀ s, plyStress M ε κ s = M *ᵥ ε + s • (M *ᵥ κ) := fun s => by
      simp only [plyStress, Matrix.mulVec_add, Matrix.mulVec_smul]
    have h1 : IntervalIntegrable (fun _ : ℝ => M *ᵥ ε) MeasureTheory.volume a b :=
      continuous_const.intervalIntegrable a b
    have h2 : IntervalIntegrable (fun s : ℝ => s • (M *ᵥ κ)) MeasureTheory.volume a b :=
      (continuous_id.smul continuous_const).intervalIntegrable a b
    calc (∫ s in a..b, plyStress M ε κ s)
        = ∫ s in a..b, (M *ᵥ ε + s • (M *ᵥ κ)) := by simp only [hstress]
      _ = (∫ s in a..b, M *ᵥ ε) + ∫ s in a..b, s • (M *ᵥ κ) :=
          intervalIntegral.integral_add h1 h2
      _ = (b - a) • (M *ᵥ ε) + ((b ^ 2 - a ^ 2) / 2) • (M *ᵥ κ) := by
          rw [intervalIntegral.integral_const, intervalIntegral.integral_smul_const, integral_id]
  simp only [forceResultant, hply, Finset.sum_add_distrib]
  congr 1
  · simp only [extensionalStiffness, Matrix.sum_mulVec, Matrix.smul_mulVec]
  · simp only [couplingStiffness, Matrix.sum_mulVec, Matrix.smul_mulVec]

/-- Integrating the ply stress moments gives the moment resultant `M = B ε⁰ + D κ`. -/
lemma momentResultant_eq (z : Fin (n + 1) → ℝ) (Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ)
    (ε κ : Fin 3 → ℝ) :
    momentResultant z Q ε κ = couplingStiffness z Q *ᵥ ε + bendingStiffness z Q *ᵥ κ := by
  have hply : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ),
      (∫ s in a..b, s • plyStress M ε κ s)
        = ((b ^ 2 - a ^ 2) / 2) • (M *ᵥ ε) + ((b ^ 3 - a ^ 3) / 3) • (M *ᵥ κ) := by
    intro M a b
    have hstress : ∀ s, s • plyStress M ε κ s = s • (M *ᵥ ε) + s ^ 2 • (M *ᵥ κ) := fun s => by
      simp only [plyStress, Matrix.mulVec_add, Matrix.mulVec_smul, smul_add]
      congr 1
      rw [← smul_assoc, smul_eq_mul, pow_two]
    have h1 : IntervalIntegrable (fun s : ℝ => s • (M *ᵥ ε)) MeasureTheory.volume a b :=
      (continuous_id.smul continuous_const).intervalIntegrable a b
    have h2 : IntervalIntegrable (fun s : ℝ => s ^ 2 • (M *ᵥ κ)) MeasureTheory.volume a b :=
      ((continuous_id.pow 2).smul continuous_const).intervalIntegrable a b
    calc (∫ s in a..b, s • plyStress M ε κ s)
        = ∫ s in a..b, (s • (M *ᵥ ε) + s ^ 2 • (M *ᵥ κ)) := by simp only [hstress]
      _ = (∫ s in a..b, s • (M *ᵥ ε)) + ∫ s in a..b, s ^ 2 • (M *ᵥ κ) :=
          intervalIntegral.integral_add h1 h2
      _ = ((b ^ 2 - a ^ 2) / 2) • (M *ᵥ ε) + ((b ^ 3 - a ^ 3) / 3) • (M *ᵥ κ) := by
          rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
            integral_id, integral_pow 2]
          norm_num
  simp only [momentResultant, hply, Finset.sum_add_distrib]
  congr 1
  · simp only [couplingStiffness, Matrix.sum_mulVec, Matrix.smul_mulVec]
  · simp only [bendingStiffness, Matrix.sum_mulVec, Matrix.smul_mulVec]

/-! ## H. Block energy and positive definiteness -/

/-- Ply decomposition of the block energy: for symmetric ply stiffnesses,
`(ε⁰, κ)ᵀ [[A, B], [B, D]] (ε⁰, κ)` is the sum over plies of the midplane square
`h i (ε⁰ + z̄ i κ)ᵀ Q̄ i (ε⁰ + z̄ i κ)` plus `h i³ κᵀ Q̄ i κ / 12`. -/
lemma abdMatrix_energy_eq (z : Fin (n + 1) → ℝ) {Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : ∀ i, (Q i)ᵀ = Q i) (ε κ : Fin 3 → ℝ) :
    Sum.elim ε κ ⬝ᵥ (abdMatrix z Q *ᵥ Sum.elim ε κ) =
      ∑ i, (plyThickness z i *
          ((ε + plyMidplane z i • κ) ⬝ᵥ (Q i *ᵥ (ε + plyMidplane z i • κ))) +
        plyThickness z i ^ 3 / 12 * (κ ⬝ᵥ (Q i *ᵥ κ))) := by
  have hsymm : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ),
      Mᵀ = M → x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
    intro M x y hM
    conv_lhs => rw [Matrix.dotProduct_mulVec, ← hM, Matrix.vecMul_transpose]
    exact dotProduct_comm _ _
  have hBsymm : (couplingStiffness z Q)ᵀ = couplingStiffness z Q := by
    simp only [couplingStiffness, Matrix.transpose_sum, Matrix.transpose_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hQ i]
  have hdotSum : ∀ (x : Fin 3 → ℝ) (f : Fin n → (Fin 3 → ℝ)),
      x ⬝ᵥ (∑ i, f i) = ∑ i, x ⬝ᵥ f i := by
    intro x f
    simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hexpand : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ), Mᵀ = M →
      (ε + c • κ) ⬝ᵥ (M *ᵥ (ε + c • κ))
        = ε ⬝ᵥ (M *ᵥ ε) + c * (ε ⬝ᵥ (M *ᵥ κ))
          + (c * (ε ⬝ᵥ (M *ᵥ κ)) + c ^ 2 * (κ ⬝ᵥ (M *ᵥ κ))) := by
    intro M c hM
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, hsymm M κ ε hM, smul_eq_mul]
    ring
  have hA : ε ⬝ᵥ (extensionalStiffness z Q *ᵥ ε)
      = ∑ i, (z i.succ - z i.castSucc) * (ε ⬝ᵥ (Q i *ᵥ ε)) := by
    simp only [extensionalStiffness, Matrix.sum_mulVec, Matrix.smul_mulVec, hdotSum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dotProduct_smul, smul_eq_mul]
  have hB : ε ⬝ᵥ (couplingStiffness z Q *ᵥ κ)
      = ∑ i, ((z i.succ ^ 2 - z i.castSucc ^ 2) / 2) * (ε ⬝ᵥ (Q i *ᵥ κ)) := by
    simp only [couplingStiffness, Matrix.sum_mulVec, Matrix.smul_mulVec, hdotSum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dotProduct_smul, smul_eq_mul]
  have hD : κ ⬝ᵥ (bendingStiffness z Q *ᵥ κ)
      = ∑ i, ((z i.succ ^ 3 - z i.castSucc ^ 3) / 3) * (κ ⬝ᵥ (Q i *ᵥ κ)) := by
    simp only [bendingStiffness, Matrix.sum_mulVec, Matrix.smul_mulVec, hdotSum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dotProduct_smul, smul_eq_mul]
  have hmain : Sum.elim ε κ ⬝ᵥ (abdMatrix z Q *ᵥ Sum.elim ε κ)
      = ε ⬝ᵥ (extensionalStiffness z Q *ᵥ ε) + ε ⬝ᵥ (couplingStiffness z Q *ᵥ κ)
        + (ε ⬝ᵥ (couplingStiffness z Q *ᵥ κ) + κ ⬝ᵥ (bendingStiffness z Q *ᵥ κ)) := by
    simp only [abdMatrix, Matrix.fromBlocks_mulVec, Matrix.dotProduct_block]
    change ε ⬝ᵥ (extensionalStiffness z Q *ᵥ ε + couplingStiffness z Q *ᵥ κ) +
        κ ⬝ᵥ (couplingStiffness z Q *ᵥ ε + bendingStiffness z Q *ᵥ κ) = _
    rw [dotProduct_add, dotProduct_add, hsymm _ κ ε hBsymm]
  rw [hmain, hA, hB, hD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hexpand (Q i) _ (hQ i)]
  simp only [plyThickness, plyMidplane]
  ring

private lemma abdMatrix_energy_pos_aux {n : ℕ} (hn : 0 < n) {z : Fin (n + 1) → ℝ}
    (hz : StrictMono z)
    {Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ} (hQ : ∀ i, (Q i).PosDef) {ε κ : Fin 3 → ℝ}
    (hεκ : ε ≠ 0 ∨ κ ≠ 0) :
    0 < Sum.elim ε κ ⬝ᵥ (abdMatrix z Q *ᵥ Sum.elim ε κ) := by
  have hQsymm : ∀ i, (Q i)ᵀ = Q i := fun i => by
    have h : (Q i)ᴴ = Q i := (hQ i).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hthick : ∀ i, 0 < plyThickness z i := fun i => by
    simp only [plyThickness]
    exact sub_pos.mpr (hz Fin.castSucc_lt_succ)
  have hSnonneg : ∀ i,
      0 ≤ (ε + plyMidplane z i • κ) ⬝ᵥ (Q i *ᵥ (ε + plyMidplane z i • κ)) := fun i => by
    have h := (hQ i).posSemidef.dotProduct_mulVec_nonneg (ε + plyMidplane z i • κ)
    rwa [star_trivial] at h
  have hKnonneg : ∀ i, 0 ≤ κ ⬝ᵥ (Q i *ᵥ κ) := fun i => by
    have h := (hQ i).posSemidef.dotProduct_mulVec_nonneg κ
    rwa [star_trivial] at h
  have hterm_nonneg : ∀ i, 0 ≤ plyThickness z i *
      ((ε + plyMidplane z i • κ) ⬝ᵥ (Q i *ᵥ (ε + plyMidplane z i • κ))) +
        plyThickness z i ^ 3 / 12 * (κ ⬝ᵥ (Q i *ᵥ κ)) := fun i => by
    have ht3 : (0 : ℝ) ≤ plyThickness z i ^ 3 / 12 :=
      div_nonneg (pow_nonneg (hthick i).le 3) (by norm_num)
    exact add_nonneg (mul_nonneg (hthick i).le (hSnonneg i)) (mul_nonneg ht3 (hKnonneg i))
  have hterm_pos : 0 < plyThickness z ⟨0, hn⟩ *
      ((ε + plyMidplane z ⟨0, hn⟩ • κ) ⬝ᵥ (Q ⟨0, hn⟩ *ᵥ (ε + plyMidplane z ⟨0, hn⟩ • κ))) +
        plyThickness z ⟨0, hn⟩ ^ 3 / 12 * (κ ⬝ᵥ (Q ⟨0, hn⟩ *ᵥ κ)) := by
    by_cases hκ0 : κ = 0
    · have hε : ε ≠ 0 := by
        rcases hεκ with h | h
        · exact h
        · exact absurd hκ0 h
      have hε0 : ε + plyMidplane z ⟨0, hn⟩ • κ = ε := by simp [hκ0]
      have hSpos : 0 < (ε + plyMidplane z ⟨0, hn⟩ • κ) ⬝ᵥ
          (Q ⟨0, hn⟩ *ᵥ (ε + plyMidplane z ⟨0, hn⟩ • κ)) := by
        rw [hε0]
        have h := (hQ ⟨0, hn⟩).dotProduct_mulVec_pos hε
        rwa [star_trivial] at h
      have ht3 : (0 : ℝ) ≤ plyThickness z ⟨0, hn⟩ ^ 3 / 12 :=
        div_nonneg (pow_nonneg (hthick ⟨0, hn⟩).le 3) (by norm_num)
      exact add_pos_of_pos_of_nonneg (mul_pos (hthick ⟨0, hn⟩) hSpos)
        (mul_nonneg ht3 (hKnonneg ⟨0, hn⟩))
    · have hKpos : 0 < κ ⬝ᵥ (Q ⟨0, hn⟩ *ᵥ κ) := by
        have h := (hQ ⟨0, hn⟩).dotProduct_mulVec_pos hκ0
        rwa [star_trivial] at h
      have h3pos : (0 : ℝ) < plyThickness z ⟨0, hn⟩ ^ 3 / 12 :=
        div_pos (pow_pos (hthick ⟨0, hn⟩) 3) (by norm_num)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (hthick ⟨0, hn⟩).le (hSnonneg ⟨0, hn⟩)) (mul_pos h3pos hKpos)
  rw [abdMatrix_energy_eq z hQsymm ε κ]
  exact lt_of_lt_of_le hterm_pos
    (Finset.single_le_sum (fun i _ => hterm_nonneg i)
      (Finset.mem_univ (⟨0, hn⟩ : Fin n)))

/-- Positive definiteness of the laminate stiffness: at least one ply, strictly increasing
interfaces and symmetric positive definite ply stiffnesses give a positive definite 6 × 6 block
stiffness, so the energy of every nonzero `(ε⁰, κ)` is positive. -/
lemma abdMatrix_posDef (hn : 0 < n) {z : Fin (n + 1) → ℝ} (hz : StrictMono z)
    {Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ} (hQ : ∀ i, (Q i).PosDef) :
    (abdMatrix z Q).PosDef := by
  have hQsymm : ∀ i, (Q i)ᵀ = Q i := fun i => by
    have h : (Q i)ᴴ = Q i := (hQ i).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hAsymm : (extensionalStiffness z Q)ᵀ = extensionalStiffness z Q := by
    simp only [extensionalStiffness, Matrix.transpose_sum, Matrix.transpose_smul, hQsymm]
  have hBsymm : (couplingStiffness z Q)ᵀ = couplingStiffness z Q := by
    simp only [couplingStiffness, Matrix.transpose_sum, Matrix.transpose_smul, hQsymm]
  have hDsymm : (bendingStiffness z Q)ᵀ = bendingStiffness z Q := by
    simp only [bendingStiffness, Matrix.transpose_sum, Matrix.transpose_smul, hQsymm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (abdMatrix z Q)ᴴ = abdMatrix z Q
    simp only [abdMatrix, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.fromBlocks_transpose, hAsymm, hBsymm, hDsymm]
  · intro x hx
    rw [star_trivial]
    have hxdecomp : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by
      funext i
      cases i <;> rfl
    rw [hxdecomp]
    have hne : (x ∘ Sum.inl) ≠ 0 ∨ (x ∘ Sum.inr) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx
      rw [hxdecomp, hcon.1, hcon.2]
      funext i
      cases i <;> rfl
    exact abdMatrix_energy_pos_aux hn hz hQ hne

/-- The block energy of every nonzero `(ε⁰, κ)` is positive, under the hypotheses of
`abdMatrix_posDef`. -/
lemma abdMatrix_energy_pos (hn : 0 < n) {z : Fin (n + 1) → ℝ} (hz : StrictMono z)
    {Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ} (hQ : ∀ i, (Q i).PosDef) {ε κ : Fin 3 → ℝ}
    (hεκ : ε ≠ 0 ∨ κ ≠ 0) :
    0 < Sum.elim ε κ ⬝ᵥ (abdMatrix z Q *ᵥ Sum.elim ε κ) := by
  exact abdMatrix_energy_pos_aux hn hz hQ hεκ

/-! ## I. Reflected stacks -/

/-- A reflected stack has no extension-bending coupling: `B = 0`. -/
lemma couplingStiffness_eq_zero_of_isReflectedStack {z : Fin (n + 1) → ℝ}
    {Q : Fin n → Matrix (Fin 3) (Fin 3) ℝ} (h : IsReflectedStack z Q) :
    couplingStiffness z Q = 0 := by
  obtain ⟨hz, hQ⟩ := h
  have hterm : ∀ i : Fin n,
      ((z i.rev.succ ^ 2 - z i.rev.castSucc ^ 2) / 2) • Q i.rev =
        -(((z i.succ ^ 2 - z i.castSucc ^ 2) / 2) • Q i) := by
    intro i
    have e1 : i.rev.succ = i.castSucc.rev := (Fin.rev_castSucc i).symm
    have e2 : i.rev.castSucc = i.succ.rev := (Fin.rev_succ i).symm
    rw [e1, e2, hz, hz, hQ i]
    have hr : ((-z i.castSucc) ^ 2 - (-z i.succ) ^ 2) / 2 =
        -((z i.succ ^ 2 - z i.castSucc ^ 2) / 2) := by ring
    rw [hr, neg_smul]
  have h1 : couplingStiffness z Q
      = ∑ i, -(((z i.succ ^ 2 - z i.castSucc ^ 2) / 2) • Q i) := by
    simp only [couplingStiffness]
    rw [← Equiv.sum_comp Fin.revPerm _]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.revPerm_apply]
    exact hterm i
  have hBB : couplingStiffness z Q = -couplingStiffness z Q := by
    nth_rewrite 1 [h1]
    rw [Finset.sum_neg_distrib]
    simp only [couplingStiffness]
  have h2 : couplingStiffness z Q + couplingStiffness z Q = 0 := by
    nth_rewrite 1 [hBB]
    exact neg_add_cancel _
  have h3 : (2 : ℝ) • couplingStiffness z Q = 0 := by
    rw [two_smul ℝ _]
    exact h2
  rcases smul_eq_zero.mp h3 with h21 | hB0
  · norm_num at h21
  · exact hB0

end Elasticity.LaminateModels

end
