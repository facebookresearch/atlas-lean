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
import Mathlib.Tactic.LinearCombination
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
  material law, and given by the inverse-congruence formula only with the MATERIAL-to-GLOBAL map;
* two plies of that lamina on `[-1, 0]` and `[0, 1]`: a reflected stack with `A = 2 Q`, `B = 0`,
  `D = (2 / 3) Q` and a positive definite block stiffness; under unit curvature no force, the
  moment `(8 / 3, 2 / 3, 0)` and the energy `8 / 3`, the sum of the two ply terms;
* a reflected three-ply stack carries no bending moment under in-plane strain;
* the balanced `±45°` pair that is not reflected has `A₁₆ = 0` but `B₁₆ = -1 / 2`: in-plane
  shear strain produces a bending moment.
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

/-! ## D. Laminates of the example lamina -/

/-- Symmetric two-ply fixture: two equal plies of the example lamina on `[-1, 0]` and `[0, 1]`.
The stack is reflected, `A = 2 Q`, `B = 0`, `D = (2 / 3) Q`, and the block stiffness is
positive definite. -/
lemma symmetricTwoPly_fixture :
    IsReflectedStack ![-1, 0, 1] ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] ∧
      extensionalStiffness ![-1, 0, 1]
          ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] =
        (2 : ℝ) • orthotropicStiffness 4 1 2 1 ∧
      couplingStiffness ![-1, 0, 1]
          ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] = 0 ∧
      bendingStiffness ![-1, 0, 1]
          ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] =
        (2 / 3 : ℝ) • orthotropicStiffness 4 1 2 1 ∧
      (abdMatrix ![-1, 0, 1]
          ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1]).PosDef := by
  have s0 : (0 : Fin 2).succ = 1 := by decide
  have c0 : (0 : Fin 2).castSucc = 0 := by decide
  have s1 : (1 : Fin 2).succ = 2 := by decide
  have c1 : (1 : Fin 2).castSucc = 1 := by decide
  have hrefl : IsReflectedStack ![-1, 0, 1]
      ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] := by
    refine ⟨?_, ?_⟩
    · intro k
      fin_cases k <;> simp
    · intro i
      fin_cases i <;> simp
  have hA : extensionalStiffness ![-1, 0, 1]
        ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] =
      (2 : ℝ) • orthotropicStiffness 4 1 2 1 := by
    simp only [extensionalStiffness, Fin.sum_univ_two, s0, c0, s1, c1]
    simp
    exact (two_smul ℝ _).symm
  have hB : couplingStiffness ![-1, 0, 1]
        ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] = 0 :=
    couplingStiffness_eq_zero_of_isReflectedStack hrefl
  have hD : bendingStiffness ![-1, 0, 1]
        ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] =
      (2 / 3 : ℝ) • orthotropicStiffness 4 1 2 1 := by
    simp only [bendingStiffness, Fin.sum_univ_two, s0, c0, s1, c1]
    simp
    have w1 : (-(-1 : ℝ) ^ 3 / 3) = 1 / 3 := by norm_num
    have w2 : ((3 : ℝ)⁻¹) = 1 / 3 := by norm_num
    rw [w1, w2, ← add_smul]
    congr 1
    norm_num
  have hz : StrictMono (![-1, 0, 1] : Fin 3 → ℝ) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hQ2 : ∀ i : Fin 2,
      (![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1] i).PosDef := by
    intro i
    fin_cases i <;> simp_all
    · exact exampleStiffness_posDef
    · exact exampleStiffness_posDef
  have hP : (abdMatrix ![-1, 0, 1]
      ![orthotropicStiffness 4 1 2 1, orthotropicStiffness 4 1 2 1]).PosDef :=
    abdMatrix_posDef (by norm_num) hz hQ2
  exact ⟨hrefl, hA, hB, hD, hP⟩

/-- Balanced but not symmetric: the example lamina at `+45°` on `[-1, 0]` and at `-45°` on
`[0, 1]`. The angle counts balance, so the shear-extension term `A₁₆` vanishes, but the stack
is not reflected and the coupling term `B₁₆` is `-1/2`. -/
lemma balancedAngleTwoPly_fixture :
    extensionalStiffness ![-1, 0, 1]
        ![globalStiffness (orthotropicStiffness 4 1 2 1) (Real.pi / 4),
          globalStiffness (orthotropicStiffness 4 1 2 1) (-(Real.pi / 4))] 0 2 = 0 ∧
      couplingStiffness ![-1, 0, 1]
        ![globalStiffness (orthotropicStiffness 4 1 2 1) (Real.pi / 4),
          globalStiffness (orthotropicStiffness 4 1 2 1) (-(Real.pi / 4))] 0 2 = -1 / 2 ∧
      ¬ IsReflectedStack ![-1, 0, 1]
        ![globalStiffness (orthotropicStiffness 4 1 2 1) (Real.pi / 4),
          globalStiffness (orthotropicStiffness 4 1 2 1) (-(Real.pi / 4))] := by
  have s0 : (0 : Fin 2).succ = 1 := by decide
  have c0 : (0 : Fin 2).castSucc = 0 := by decide
  have s1 : (1 : Fin 2).succ = 2 := by decide
  have c1 : (1 : Fin 2).castSucc = 1 := by decide
  have hentry : ∀ θ : ℝ, globalStiffness (orthotropicStiffness 4 1 2 1) θ 0 2
      = Real.cos θ * Real.sin θ := by
    intro θ
    simp [globalStiffness, strainMap, orthotropicStiffness, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.transpose_apply]
    linear_combination (Real.cos θ * Real.sin θ) * Real.cos_sq_add_sin_sq θ
  have hcs : Real.cos (Real.pi / 4) * Real.sin (Real.pi / 4) = 1 / 2 := by
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four, div_mul_div_comm,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hplus : globalStiffness (orthotropicStiffness 4 1 2 1) (Real.pi / 4) 0 2 = 1 / 2 := by
    rw [hentry]
    exact hcs
  have hminus : globalStiffness (orthotropicStiffness 4 1 2 1) (-(Real.pi / 4)) 0 2
      = -(1 / 2) := by
    rw [hentry, Real.cos_neg, Real.sin_neg, mul_neg, hcs]
  have hA : extensionalStiffness ![-1, 0, 1]
        ![globalStiffness (orthotropicStiffness 4 1 2 1) (Real.pi / 4),
          globalStiffness (orthotropicStiffness 4 1 2 1) (-(Real.pi / 4))] 0 2 = 0 := by
    simp only [extensionalStiffness, Fin.sum_univ_two, s0, c0, s1, c1,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simp
    rw [hplus, hminus]
    norm_num
  have hB : couplingStiffness ![-1, 0, 1]
        ![globalStiffness (orthotropicStiffness 4 1 2 1) (Real.pi / 4),
          globalStiffness (orthotropicStiffness 4 1 2 1) (-(Real.pi / 4))] 0 2 = -1 / 2 := by
    simp only [couplingStiffness, Fin.sum_univ_two, s0, c0, s1, c1,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simp
    rw [hplus, hminus]
    norm_num
  have hnot : ¬ IsReflectedStack ![-1, 0, 1]
        ![globalStiffness (orthotropicStiffness 4 1 2 1) (Real.pi / 4),
          globalStiffness (orthotropicStiffness 4 1 2 1) (-(Real.pi / 4))] := by
    intro h
    obtain ⟨hz, hQ⟩ := h
    have r0 : (0 : Fin 2).rev = 1 := by decide
    have h0 := hQ 0
    rw [r0] at h0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0
    have h02 : globalStiffness (orthotropicStiffness 4 1 2 1) (-(Real.pi / 4)) 0 2
        = globalStiffness (orthotropicStiffness 4 1 2 1) (Real.pi / 4) 0 2 := by
      rw [h0]
    rw [hminus, hplus] at h02
    norm_num at h02
  exact ⟨hA, hB, hnot⟩

-- Under unit curvature the symmetric two-ply laminate carries no force resultant and the moment
-- `D κ = (2 / 3) (4, 1, 0)`.
example :
    forceResultant ![-1, 0, 1] ![exampleStiffness, exampleStiffness] 0 ![1, 0, 0] = 0 ∧
      momentResultant ![-1, 0, 1] ![exampleStiffness, exampleStiffness] 0 ![1, 0, 0] =
        ![8 / 3, 2 / 3, 0] := by
  obtain ⟨-, -, hB, hD, -⟩ := symmetricTwoPly_fixture
  simp only [exampleStiffness]
  rw [forceResultant_eq, momentResultant_eq, hB, hD]
  refine ⟨by simp, ?_⟩
  ext i
  fin_cases i <;> norm_num [orthotropicStiffness]

-- Its energy under unit curvature is `8 / 3`, the sum of the two ply terms
-- `1 · (1 / 2)² · 4 + 1³ · 4 / 12 = 4 / 3`.
example :
    Sum.elim 0 ![1, 0, 0] ⬝ᵥ
        (abdMatrix ![-1, 0, 1] ![exampleStiffness, exampleStiffness] *ᵥ Sum.elim 0 ![1, 0, 0]) =
      8 / 3 := by
  have hsym : exampleStiffnessᵀ = exampleStiffness := by
    have h := exampleStiffness_posDef.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [abdMatrix_energy_eq _ (fun i => by fin_cases i <;> exact hsym)]
  simp [Fin.sum_univ_two, plyThickness, plyMidplane, exampleStiffness, orthotropicStiffness,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  norm_num

-- Every nonzero curvature costs positive energy in the symmetric two-ply laminate.
example {κ : Fin 3 → ℝ} (hκ : κ ≠ 0) :
    0 < Sum.elim 0 κ ⬝ᵥ
      (abdMatrix ![-1, 0, 1] ![exampleStiffness, exampleStiffness] *ᵥ Sum.elim 0 κ) := by
  refine abdMatrix_energy_pos (by norm_num) ?_ (fun i => ?_) (Or.inr hκ)
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · fin_cases i <;> exact exampleStiffness_posDef

-- A reflected three-ply stack (outer plies the example lamina, middle ply its own mirror) has
-- `B = 0`, so in-plane strain alone produces no bending moment.
example (ε : Fin 3 → ℝ) :
    momentResultant ![-3 / 2, -1 / 2, 1 / 2, 3 / 2]
      ![exampleStiffness, orthotropicStiffness 2 1 4 1, exampleStiffness] ε 0 = 0 := by
  have hrefl : IsReflectedStack ![-3 / 2, -1 / 2, 1 / 2, 3 / 2]
      ![exampleStiffness, orthotropicStiffness 2 1 4 1, exampleStiffness] := by
    refine ⟨fun k => ?_, fun i => ?_⟩
    · fin_cases k <;> simp <;> norm_num
    · fin_cases i <;> simp
  rw [momentResultant_eq, couplingStiffness_eq_zero_of_isReflectedStack hrefl]
  simp

-- In the balanced but unreflected `±45°` pair, in-plane shear strain produces the bending moment
-- `M₁ = B₁₆ = -1 / 2`.
example :
    momentResultant ![-1, 0, 1]
        ![globalStiffness exampleStiffness (Real.pi / 4),
          globalStiffness exampleStiffness (-(Real.pi / 4))] ![0, 0, 1] 0 0 = -1 / 2 := by
  obtain ⟨-, hB, -⟩ := balancedAngleTwoPly_fixture
  simp only [exampleStiffness]
  rw [momentResultant_eq]
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hB

end PhyslibExtTest.Elasticity.LaminateModels

end
