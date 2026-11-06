/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02FastTensorStateAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalInverse

/-! The complete genuine original root-2 source and both actual triality outputs have exact rational coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original physical source matrix, preferred short coefficient, and scaled tensor coefficient. -/
def generatedAxisGlobalOddRoot02RationalPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalOddRootMatrixQ 2,
    (generatedAxisGlobalOddOtherSparseShortQ 0,
      fun t j => (generatedAxisGlobalOddRoot02Spin11 (generatedAxisGlobalSpinLabel t) : ℚ) *
        (generatedAxisGlobalOddRoot02Spatial11 j : ℚ) / 8))

/-- The complete rational packet is exactly the actual original root-2 local action. -/
theorem generatedAxisGlobalOddRoot02RationalPacket_actual :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal generatedAxisGlobalOddRoot02RationalPacket := by
  apply Prod.ext
  · exact generatedAxisGlobalOddRootMatrix_actual 2
  · apply Prod.ext
    · funext r
      rw [generatedAxisGlobalOddRootShortQ_actual, generatedAxisGlobalOddOtherSparseShortQ_root02]
      rfl
    · rw [generatedAxisGlobalOddRoot02FastTensorState_actual,
        generatedAxisGlobalTensorFactor_rational]
      rfl

/-- Every positive transition coefficient comes from the genuine original triality operator. -/
theorem generatedAxisGlobalOddRoot02PositiveRationalPacket_actual :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalTriality generatedAxisGlobalOddRoot02RationalPacket) :=
  generatedAxisGlobalRationalTriality_of_actual _ _ generatedAxisGlobalOddRoot02RationalPacket_actual

/-- Every negative transition coefficient uses the genuine inverse original triality operator. -/
theorem generatedAxisGlobalOddRoot02NegativeRationalPacket_actual :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalInverse generatedAxisGlobalOddRoot02RationalPacket) :=
  generatedAxisGlobalRationalInverse_actual _ _ generatedAxisGlobalOddRoot02RationalPacket_actual

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
