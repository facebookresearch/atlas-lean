/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialTensorFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRecognition

/-! Actual matrix fixation of the genuine full-phase corrected flag lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The corrected actual lift fixes the entire original fourth-axis matrix block. -/
theorem generatedFourth_monomial_matrix_fixed (k : Fin 4) :
    conwayMatrixAction (generatedFourthMonomialCorrectedFiber k).val.2
      (griessConwayEncode generatedFourthAxis).1 = (griessConwayEncode generatedFourthAxis).1 := by
  apply (generatedFourth_matrix_stabilizer_iff _).mpr
  rw [generatedFourth_monomial_corrected_spatial]
  exact generatedFourth_monomial_flag_mem k

/-- Original short-coordinate fixation completes the actual three-block axis-fix criterion. -/
theorem generatedFourth_monomial_axis_fixed_of_short (k : Fin 4)
    (hs : localShortOperator (generatedFourthMonomialCorrectedFiber k)
      (griessConwayEncode generatedFourthAxis).2.1 =
        (griessConwayEncode generatedFourthAxis).2.1) :
    rhoLocal (localFiberIntoH (generatedFourthMonomialCorrectedFiber k)) generatedFourthAxis =
      generatedFourthAxis := by
  have he : griessConwayEncode
      (localGriessRepresentation (generatedFourthMonomialCorrectedFiber k) generatedFourthAxis) =
        griessConwayEncode generatedFourthAxis := by
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    apply Prod.ext
    · exact generatedFourth_monomial_matrix_fixed k
    · apply Prod.ext
      · exact hs
      · exact generatedFourth_monomial_tensor_fixed k
  have hd := congrArg griessConwayDecode he
  change localGriessRepresentation (generatedFourthMonomialCorrectedFiber k) generatedFourthAxis = _
  simpa only [griessConwayDecode_encode] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
