/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Elasticity.LaminateModels
public import PhyslibExt.Units.EngineeringFrames
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Elasticity.LaminateModels`

* at 45 degrees a uniaxial strain and a uniaxial stress carry nonzero material shear, the work is
  the same in both frames, and the stress map agrees with the existing tensor rotation;
* tensor shear without the factor two gives the material-axes pairing `3 / 4` against the global
  `1`;
* an orthotropic lamina `Q₁₁ = 4`, `Q₁₂ = 1`, `Q₂₂ = 2`, `Q₆₆ = 1`: positive definite, with the
  45-degree global stiffness of shear coupling `1 / 2`, positive definite again, reproducing the
  material law, and given by the inverse-congruence formula only with the MATERIAL-to-GLOBAL map.
-/

@[expose] public section

open scoped Matrix

namespace PhyslibExtTest.Elasticity.LaminateModels

open _root_.Elasticity.LaminateModels _root_.Units.EngineeringFrames

/-! ## A. Private 45-degree computations -/

private lemma degToRad_45 : degToRad 45 = Real.pi / 4 := by
  unfold degToRad
  ring

private lemma cos_degToRad_45 : Real.cos (degToRad 45) = Real.sqrt 2 / 2 := by
  rw [degToRad_45]
  exact Real.cos_pi_div_four

private lemma sin_degToRad_45 : Real.sin (degToRad 45) = Real.sqrt 2 / 2 := by
  rw [degToRad_45]
  exact Real.sin_pi_div_four

private lemma sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

private lemma cos_sq_degToRad_45 : Real.cos (degToRad 45) ^ 2 = 1 / 2 := by
  rw [cos_degToRad_45, div_pow, sqrt_two_sq]
  norm_num

private lemma sin_sq_degToRad_45 : Real.sin (degToRad 45) ^ 2 = 1 / 2 := by
  rw [sin_degToRad_45, div_pow, sqrt_two_sq]
  norm_num

private lemma cos_mul_sin_degToRad_45 :
    Real.cos (degToRad 45) * Real.sin (degToRad 45) = 1 / 2 := by
  have hfactor : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) =
      (Real.sqrt 2 * Real.sqrt 2) / 4 := by ring
  rw [cos_degToRad_45, sin_degToRad_45, hfactor, sqrt_two_mul_self]
  norm_num

private lemma two_cos_mul_sin_degToRad_45 :
    2 * Real.cos (degToRad 45) * Real.sin (degToRad 45) = 1 := by
  have hfactor : 2 * Real.cos (degToRad 45) * Real.sin (degToRad 45) =
      2 * (Real.cos (degToRad 45) * Real.sin (degToRad 45)) := by ring
  rw [hfactor, cos_mul_sin_degToRad_45]
  norm_num

private lemma cos_sq_sub_sin_sq_degToRad_45 :
    Real.cos (degToRad 45) ^ 2 - Real.sin (degToRad 45) ^ 2 = 0 := by
  rw [cos_sq_degToRad_45, sin_sq_degToRad_45]
  norm_num

private lemma strainMap_degToRad_45_mulVec :
    strainMap (degToRad 45) *ᵥ ![1, 0, 0] = ![1 / 2, 1 / 2, -1] := by
  ext i
  fin_cases i <;>
    simp [strainMap, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
      cos_sq_degToRad_45, sin_sq_degToRad_45, two_cos_mul_sin_degToRad_45]

private lemma stressMap_degToRad_45_mulVec :
    stressMap (degToRad 45) *ᵥ ![1, 0, 0] = ![1 / 2, 1 / 2, -1 / 2] := by
  ext i
  fin_cases i <;>
    norm_num [stressMap, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
      cos_sq_degToRad_45, sin_sq_degToRad_45, cos_mul_sin_degToRad_45]

/-! ## B. Uniaxial loads and the shear factor at 45 degrees -/

/-- At 45 degrees a global uniaxial strain and a global uniaxial stress carry nonzero material
shear: `T_e (1, 0, 0) = (1/2, 1/2, -1)` and `T_s (1, 0, 0) = (1/2, 1/2, -1/2)`; the work is `1`
in both frames. -/
lemma uniaxial_fixture :
    strainMap (degToRad 45) *ᵥ ![1, 0, 0] = ![1 / 2, 1 / 2, -1] ∧
      stressMap (degToRad 45) *ᵥ ![1, 0, 0] = ![1 / 2, 1 / 2, -1 / 2] ∧
      (stressMap (degToRad 45) *ᵥ ![1, 0, 0]) ⬝ᵥ (strainMap (degToRad 45) *ᵥ ![1, 0, 0]) = 1 := by
  refine ⟨strainMap_degToRad_45_mulVec, stressMap_degToRad_45_mulVec, ?_⟩
  rw [stressMap_degToRad_45_mulVec, strainMap_degToRad_45_mulVec]
  norm_num [dotProduct, Fin.sum_univ_three]

/-- Tensor shear without the factor two breaks energy invariance: tensor strain components
`(ε_xx, ε_yy, ε_xy)` transform with the stress map, and their plain pairing with the stress at
45 degrees, for uniaxial stress and strain `(1, 0, 0)`, is `3 / 4` in material axes against `1`
in global axes. -/
lemma tensorShear_fixture :
    (stressMap (degToRad 45) *ᵥ ![1, 0, 0]) ⬝ᵥ (stressMap (degToRad 45) *ᵥ ![1, 0, 0]) = 3 / 4 ∧
      (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 0, 0] = 1 := by
  refine ⟨?_, ?_⟩
  · rw [stressMap_degToRad_45_mulVec]
    norm_num [dotProduct, Fin.sum_univ_three]
  · norm_num [dotProduct, Fin.sum_univ_three]

-- The stress map agrees with the existing tensor rotation: at 45 degrees the uniaxial stress
-- `diag(1, 0)` has material components `(1/2, 1/2, -1/2)`.
example :
    stressVoigt (_root_.Elasticity.rotatedStress2 !![1, 0; 0, 0] (degToRad 45)) =
      ![1 / 2, 1 / 2, -1 / 2] := by
  have hσ : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hv : stressVoigt !![(1 : ℝ), 0; 0, 0] = ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [stressVoigt]
  rw [← stressMap_mulVec_stressVoigt (degToRad 45) hσ, hv, uniaxial_fixture.2.1]

-- Work invariance at 45 degrees from the duality alone: the uniaxial stress does the work `1` on
-- the uniaxial strain in material axes.
example :
    (stressMap (degToRad 45) *ᵥ ![1, 0, 0]) ⬝ᵥ (strainMap (degToRad 45) *ᵥ ![1, 0, 0]) = 1 := by
  rw [stressMap_mulVec_dotProduct_strainMap_mulVec]
  simp [dotProduct, Fin.sum_univ_three]

-- The shear entry of the engineering strain is the existing engineering shear `2 ε₀₁`.
example (ε : Matrix (Fin 3) (Fin 3) ℝ) : strainVoigt (inPlane ε) 2 = 2 * ε 0 1 := by
  rw [strainVoigt_inPlane_two]
  rfl

/-! ## C. An orthotropic lamina at 45 degrees -/

/-- Example orthotropic lamina: `Q₁₁ = 4`, `Q₁₂ = 1`, `Q₂₂ = 2`, `Q₆₆ = 1` (in units of 10 GPa). -/
def exampleStiffness : Matrix (Fin 3) (Fin 3) ℝ :=
  orthotropicStiffness 4 1 2 1

/-- The example stiffness is positive definite. -/
lemma exampleStiffness_posDef : exampleStiffness.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · show exampleStiffnessᴴ = exampleStiffness
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [exampleStiffness, orthotropicStiffness, Matrix.transpose_apply]
  · intro x hx
    have hform : star x ⬝ᵥ (exampleStiffness *ᵥ x) =
        3 * (x 0) ^ 2 + (x 0 + x 1) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
      simp [exampleStiffness, orthotropicStiffness, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two]
      ring
    rw [hform]
    have hex : ∃ i, x i ≠ 0 := by
      have hne := Function.ne_iff.mp hx
      simpa using hne
    obtain ⟨i, hi⟩ := hex
    fin_cases i
    · have hi0 : x 0 ≠ 0 := hi
      nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1), sq_nonneg (x 2),
        mul_self_pos.mpr hi0]
    · have hi1 : x 1 ≠ 0 := hi
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 0 + x 1), sq_nonneg (x 2),
        mul_self_pos.mpr hi1]
    · have hi2 : x 2 ≠ 0 := hi
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 0 + x 1), sq_nonneg (x 1),
        mul_self_pos.mpr hi2]

/-- At 45 degrees the example lamina has the global stiffness with nonzero shear coupling
`Q₁₆ = Q₂₆ = 1 / 2`. -/
lemma globalStiffness_example :
    globalStiffness exampleStiffness (degToRad 45) =
      !![3, 1, 1 / 2; 1, 3, 1 / 2; 1 / 2, 1 / 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [globalStiffness, exampleStiffness, orthotropicStiffness, strainMap,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.transpose_apply,
      cos_sq_degToRad_45, sin_sq_degToRad_45, cos_mul_sin_degToRad_45,
      two_cos_mul_sin_degToRad_45, cos_sq_sub_sin_sq_degToRad_45]

/-- The inverse-congruence formula with the GLOBAL-to-MATERIAL map gives a different matrix
for the example lamina at 45 degrees. -/
lemma inv_congr_example_ne :
    ((strainMap (degToRad 45))⁻¹)ᵀ * exampleStiffness * (strainMap (degToRad 45))⁻¹ ≠
      globalStiffness exampleStiffness (degToRad 45) := by
  rw [inv_congr_strainMap]
  have hnsq : (-Real.sin (degToRad 45)) ^ 2 = Real.sin (degToRad 45) ^ 2 := by ring
  have h1 : globalStiffness exampleStiffness (-(degToRad 45)) 0 2 = -1 / 2 := by
    norm_num [globalStiffness, exampleStiffness, orthotropicStiffness, strainMap,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.transpose_apply,
      Real.cos_neg, Real.sin_neg, hnsq, cos_sq_degToRad_45, sin_sq_degToRad_45,
      cos_mul_sin_degToRad_45, two_cos_mul_sin_degToRad_45, cos_sq_sub_sin_sq_degToRad_45]
  have h2 : globalStiffness exampleStiffness (degToRad 45) 0 2 = 1 / 2 := by
    rw [globalStiffness_example]
    simp
  intro hcon
  have hcontra := congrArg (fun M => M 0 2) hcon
  rw [h1, h2] at hcontra
  norm_num at hcontra

-- The 45-degree global stiffness of the example lamina is positive definite, by congruence.
example : (globalStiffness exampleStiffness (degToRad 45)).PosDef :=
  globalStiffness_posDef exampleStiffness_posDef (degToRad 45)

-- It reproduces the material law for every global strain.
example (e : Fin 3 → ℝ) :
    stressMap (degToRad 45) *ᵥ (globalStiffness exampleStiffness (degToRad 45) *ᵥ e) =
      exampleStiffness *ᵥ (strainMap (degToRad 45) *ᵥ e) :=
  (stressMap_mulVec_eq_iff_eq_globalStiffness exampleStiffness _ (degToRad 45)).2 rfl e

-- The inverse-congruence formula gives it with the MATERIAL-to-GLOBAL map `T_e(-45°)`.
example :
    ((strainMap (-degToRad 45))⁻¹)ᵀ * exampleStiffness * (strainMap (-degToRad 45))⁻¹ =
      !![3, 1, 1 / 2; 1, 3, 1 / 2; 1 / 2, 1 / 2, 1] := by
  rw [← globalStiffness_eq_inv_congr, globalStiffness_example]

end PhyslibExtTest.Elasticity.LaminateModels

end
