/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftTensorFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRecognition

/-! Actual matrix fixation of the genuine full-phase corrected flag lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine extraspecial correction leaves the actual spatial component unchanged. -/
theorem generatedFourth_flag_corrected_lift_spatial :
    generatedFourthFlagCorrectedLift.val.2 = generatedFourthFlagNormalizedLift.val.2 := by
  change 1 * generatedFourthFlagNormalizedLift.val.2 = _
  exact one_mul _

/-- The corrected actual lift fixes the entire original fourth-axis matrix block. -/
theorem generatedFourth_flag_corrected_lift_matrix_fixed :
    conwayMatrixAction generatedFourthFlagCorrectedLift.val.2
      (griessConwayEncode generatedFourthAxis).1 = (griessConwayEncode generatedFourthAxis).1 := by
  apply (generatedFourth_matrix_stabilizer_iff _).mpr
  rw [generatedFourth_flag_corrected_lift_spatial]
  exact generatedFourth_flag_lift_mem

/-- Original short-coordinate fixation completes the actual three-block axis-fix criterion. -/
theorem generatedFourth_flag_corrected_lift_fixed_of_short
    (hs : localShortOperator generatedFourthFlagCorrectedLift
      (griessConwayEncode generatedFourthAxis).2.1 =
        (griessConwayEncode generatedFourthAxis).2.1) :
    rhoLocal (localFiberIntoH generatedFourthFlagCorrectedLift) generatedFourthAxis =
      generatedFourthAxis := by
  have he : griessConwayEncode
      (localGriessRepresentation generatedFourthFlagCorrectedLift generatedFourthAxis) =
        griessConwayEncode generatedFourthAxis := by
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    apply Prod.ext
    · exact generatedFourth_flag_corrected_lift_matrix_fixed
    · apply Prod.ext
      · exact hs
      · exact generatedFourth_flag_corrected_lift_tensor_fixed
  have hd := congrArg griessConwayDecode he
  change localGriessRepresentation generatedFourthFlagCorrectedLift generatedFourthAxis = _
  simpa only [griessConwayDecode_encode] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
