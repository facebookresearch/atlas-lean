/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthInputTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor

/-! The entire true ninth middle tensor retains the original spin and physical factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete integer numerator, using the genuine nine-factor spin word in each column. -/
def generatedNinthMiddleTensorInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ j : Fin 24, generatedNinthFrameVectorData 9 j i *
    generatedNinthIntegerSpin (generatedNinthInputTensorInteger j) n

/-- Every actual middle coordinate is the exact integral numerator with its full denominator. -/
theorem generatedNinth_middle_tensor_integer (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.2 t i =
        (generatedNinthMiddleTensorInteger (nortonUIntegerLabel t) i : ℝ) /
          (32768 * Real.sqrt 2) := by
  change (griessConwayEncode
    (localGriessRepresentation generatedNinthLocalFiber generatedFifthAxis)).2.2 t i = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor,
    generatedFourth_local_tensor_columns]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  calc
    _ = ∑ j : Fin 24, ((generatedNinthFrameVectorData 9 j i : ℝ) *
        (generatedNinthIntegerSpin (generatedNinthInputTensorInteger j)
          (nortonUIntegerLabel t) : ℝ)) / (32768 * Real.sqrt 2) := by
      apply Finset.sum_congr rfl
      intro j _
      change leechIsomMatrix generatedNinthLocalFiber.val.2 i j *
        generatedNinthLocalFiber.val.1.val
          (fun u => (griessConwayEncode generatedFifthAxis).2.2 u j) t = _
      rw [generatedNinth_forward_matrix_coordinate, generatedNinth_input_tensor_embed,
        map_smul, generatedNinth_integer_spin_embed]
      simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
      field_simp [hs]
      ring
    _ = _ := by
      rw [← Finset.sum_div]
      simp only [generatedNinthMiddleTensorInteger, Int.cast_sum, Int.cast_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
