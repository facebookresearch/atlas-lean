/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorIntegerData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor

/-! Complete actual tensor action of the original Q-corrected inverse-C, Xi, C generator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original tensor column has its genuine checked integer spin-vector embedding. -/
theorem generatedSixth_tensor_column_embed (j : Fin 24) :
    (fun t => (griessConwayEncode generatedSixthAxis).2.2 t j) =
      (1 / (32 * Real.sqrt 2) : ℝ) •
        nortonUIntegerEmbed (fun n => generatedSixthTensorExecutable n j) := by
  funext t
  have h := generatedSixth_tensor_executable (nortonUIntegerLabel t) j
  rw [nortonUIntegerLabel_inverse] at h
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
  exact h.trans (by ring)

/-- The genuine original raw tensor action is the complete cleared integer numerator. -/
theorem generatedSixth_xi_raw_tensor_integer (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedSixthRawGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.2 t i =
        (generatedSixthXiRawTensorInteger (nortonUIntegerLabel t) i : ℝ) /
          (512 * Real.sqrt 2) := by
  have hphys (j : Fin 24) :
      (generatedSixthRawGenerator 4).val.2.val (Pi.single j 1) i =
        (1 / 2 : ℝ) * (sixthFrameOrbitSpatialNumerator 14 i j : ℝ) := by
    have h := sixthFrameOrbit_original_physical_matrix 14
    change leechIsomMatrix (generatedSixthRawGenerator 4).val.2 =
      (1 / 2 : ℝ) • (sixthFrameOrbitSpatialNumerator 14).map (Int.castRingHom ℝ) at h
    exact congrFun (congrFun h i) j
  have hspin (j : Fin 24) :
      (generatedSixthRawGenerator 4).val.1.val
        (fun u => (griessConwayEncode generatedSixthAxis).2.2 u j) t =
      (generatedSixthXiSpinInteger (fun n => generatedSixthTensorExecutable n j)
        (nortonUIntegerLabel t) : ℝ) / (256 * Real.sqrt 2) := by
    rw [generatedSixth_tensor_column_embed, map_smul, generatedSixth_xi_spin_integer_embed]
    simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp [hs]
    ring
  rw [generatedFourth_local_tensor_columns]
  calc
    _ = ∑ j : Fin 24, ((sixthFrameOrbitSpatialNumerator 14 i j : ℝ) *
        (generatedSixthXiSpinInteger (fun n => generatedSixthTensorExecutable n j)
          (nortonUIntegerLabel t) : ℝ)) / (512 * Real.sqrt 2) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hphys, hspin]
      have hs : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hs]
      ring
    _ = _ := by
      rw [← Finset.sum_div]
      simp only [generatedSixthXiRawTensorInteger, Int.cast_sum, Int.cast_mul]

/-- The actual full corrected-Xi tensor coordinate includes its preferred central Q sign. -/
theorem generatedSixth_xi_corrected_tensor_integer (n : Fin 4096) (i : Fin 24) :
    localTensorRepresentation (generatedSixthCorrectedGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) i =
        (generatedSixthXiTensorInteger n i : ℝ) / (512 * Real.sqrt 2) := by
  rw [generatedSixthCorrectedGenerator, map_mul, LinearEquiv.mul_apply,
    generatedFourth_lift_q_tensor, generatedSixth_xi_raw_tensor_integer]
  simp only [generatedSixthXiTensorInteger, Int.cast_mul, nortonUIntegerSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
