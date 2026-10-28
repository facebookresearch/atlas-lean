/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorState
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTrialityTensor

/-! The actual outgoing tensor column combines a controlled old Y row and one high odd row. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual twentieth tensor column with its original common denominator cleared. -/
def generatedEighthTensorColumn (t : SpinIndex) : ℝ :=
  32 * Real.sqrt 2 * (griessConwayEncode generatedEighthAxis).2.2 t 20

/-- The incoming odd-short contribution to that actual denominator-cleared column. -/
def generatedEighthTensorXContribution (t : SpinIndex) : ℝ :=
  32 * qSign (t 11) *
    (if (golayEncodedMask (spinDictionaryCode t).val).testBit (20 : Fin 24).val then -1 else 1) *
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (spinDictionaryCode t, 20)))

/-- The outgoing tensor column retains both original dictionary contributions. -/
theorem generatedEighth_tensor_column_coordinate (t : SpinIndex) :
    generatedEighthTensorColumn t =
      generatedEighthTensorXContribution t + generatedEighthTensorYContribution t 20 := by
  unfold generatedEighthTensorColumn
  rw [generatedEighthAxis_local_expression, generatedSixth_triality_tensor_coordinate]
  simp only [trialityYTensor, ite_true, mul_one]
  unfold generatedEighthTensorXContribution generatedEighthTensorYContribution
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- The original odd contribution retains exactly 1024 times its incoming coefficient square. -/
theorem generatedEighth_tensor_X_square (t : SpinIndex) :
    (generatedEighthTensorXContribution t) ^ 2 = 1024 *
      ((griessConwayEncode
        (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1
          (Sum.inr (Sum.inr (spinDictionaryCode t, 20)))) ^ 2 := by
  unfold generatedEighthTensorXContribution
  rw [mul_pow, mul_pow, mul_pow, pow_two (qSign _), qSign_sq]
  split_ifs <;> ring

/-- The odd contribution changes sign on the second address of the original omega pair. -/
theorem generatedEighth_tensor_X_omega (t : SpinIndex) :
    generatedEighthTensorXContribution (t + Pi.single (11 : Fin 12) 1) =
      -generatedEighthTensorXContribution t := by
  unfold generatedEighthTensorXContribution
  simp only [spinDictionaryCode_add_omega, Pi.add_apply, Pi.single_eq_same, qSign_add,
    qSign_one]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
