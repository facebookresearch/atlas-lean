/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignData

/-! Complete original tensor fixation by the twelve Q-corrected source Golay sign words. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual local fiber consisting of correcting Q followed by the original source sign word. -/
noncomputable def generatedFifthSignCorrectedFiber (k : Fin 12) : localFiberSubgroup :=
  localFiberIncl (generatedFifthSignCorrection k) *
    generatedFifthSignFiber (generatedFifthSignCode k) 0

/-- Each original supported Y state is fixed by the complete actual corrected tensor action. -/
theorem generatedFifth_sign_tensor_state_fixed (k : Fin 12) (j : Fin 64) :
    localTensorRepresentation (generatedFifthSignCorrectedFiber k)
      (trialityYTensor (generatedFifthOddRootOutputData j).1
        (generatedFifthOddRootOutputData j).2) =
      trialityYTensor (generatedFifthOddRootOutputData j).1
        (generatedFifthOddRootOutputData j).2 := by
  rw [generatedFifthSignCorrectedFiber, map_mul, LinearEquiv.mul_apply]
  rw [generatedFifth_sign_tensor_Y _ 0 _ _ _
    (generatedFifth_sign_output_translation k j) _]
  rw [map_smul]
  ext t i
  change qSign (generatedFifthSignDictionaryPhase (sourceQCode (generatedFifthSignCode k) 0)
    (generatedFifthOddRootOutputData j).1 (generatedFifthSignOutput k j)) *
      localTensorRepresentation (localFiberIncl (generatedFifthSignCorrection k))
        (trialityYTensor (generatedFifthSignOutput k j)
          (generatedFifthOddRootOutputData j).2) t i = _
  rw [localTensorRepresentation_q]
  have hc := generatedFifth_sign_corrected_Y (generatedFifthSignCorrection k)
    (generatedFifthOddRootOutputData j).1 (generatedFifthSignOutput k j) _ _
    (generatedFifth_sign_correction_translation k j)
    (generatedFifth_sign_correction_omega k) (generatedFifthOddRootOutputData j).2 i
    (generatedFifth_sign_correction_phase k j)
  rw [congrFun hc t, ← mul_assoc, qSign_sq, one_mul]

/-- Every one of the twelve actual corrected sign words fixes the complete original tensor. -/
theorem generatedFifth_sign_tensor_fixed (k : Fin 12) :
    localTensorRepresentation (generatedFifthSignCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2 := by
  rw [generatedFifth_tensor_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, generatedFifth_sign_tensor_state_fixed]

/-- The actual original Griess action fixes its entire tensor coordinate. -/
theorem generatedFifth_sign_encoded_tensor_fixed (k : Fin 12) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k))
      generatedFifthAxis)).2.2 = (griessConwayEncode generatedFifthAxis).2.2 := by
  rw [generatedFourth_local_tensor, generatedFifth_sign_tensor_fixed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
