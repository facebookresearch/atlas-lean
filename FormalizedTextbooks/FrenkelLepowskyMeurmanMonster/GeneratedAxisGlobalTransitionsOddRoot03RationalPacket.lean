/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03FastTensorStateAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalInverse

/-! The complete genuine original root-3 source and both actual triality outputs have exact rational coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original physical source matrix, preferred short coefficient, and scaled tensor coefficient. -/
def generatedAxisGlobalOddRoot03RationalPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalOddRootMatrixQ 3,
    (generatedAxisGlobalOddOtherSparseShortQ 1,
      fun t j => (generatedAxisGlobalOddRoot03Spin09 (generatedAxisGlobalSpinLabel t) : ℚ) *
        (generatedAxisGlobalOddRoot03Spatial09 j : ℚ) / 8))

/-- The complete rational packet is exactly the actual original root-3 local action. -/
theorem generatedAxisGlobalOddRoot03RationalPacket_actual :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3) generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal generatedAxisGlobalOddRoot03RationalPacket := by
  apply Prod.ext
  · exact generatedAxisGlobalOddRootMatrix_actual 3
  · apply Prod.ext
    · funext r
      rw [generatedAxisGlobalOddRootShortQ_actual, generatedAxisGlobalOddOtherSparseShortQ_root03]
      rfl
    · rw [generatedAxisGlobalOddRoot03FastTensorState_actual,
        generatedAxisGlobalTensorFactor_rational]
      rfl

/-- Every positive transition coefficient comes from the genuine original triality operator. -/
theorem generatedAxisGlobalOddRoot03PositiveRationalPacket_actual :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3) generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalTriality generatedAxisGlobalOddRoot03RationalPacket) :=
  generatedAxisGlobalRationalTriality_of_actual _ _ generatedAxisGlobalOddRoot03RationalPacket_actual

/-- Every negative transition coefficient uses the genuine inverse original triality operator. -/
theorem generatedAxisGlobalOddRoot03NegativeRationalPacket_actual :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3) generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalInverse generatedAxisGlobalOddRoot03RationalPacket) :=
  generatedAxisGlobalRationalInverse_actual _ _ generatedAxisGlobalOddRoot03RationalPacket_actual

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
