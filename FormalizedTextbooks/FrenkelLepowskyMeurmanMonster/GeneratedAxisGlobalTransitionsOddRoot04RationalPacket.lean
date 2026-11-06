/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04FastTensorStateAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalInverse

/-! The complete genuine original root-four source and both actual triality outputs have exact rational coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original physical source matrix, preferred short coefficient, and scaled tensor coefficient. -/
def generatedAxisGlobalOddRoot04RationalPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalOddRootMatrixQ 4,
    (generatedAxisGlobalOddOtherSparseShortQ 2,
      fun t j => (generatedAxisGlobalOddRoot04Spin09 (generatedAxisGlobalSpinLabel t) : ℚ) *
        (generatedAxisGlobalOddRoot04Spatial09 j : ℚ) / 4))

/-- The complete rational packet is exactly the actual original root-four local action. -/
theorem generatedAxisGlobalOddRoot04RationalPacket_actual :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal generatedAxisGlobalOddRoot04RationalPacket := by
  apply Prod.ext
  · exact generatedAxisGlobalOddRootMatrix_actual 4
  · apply Prod.ext
    · funext r
      rw [generatedAxisGlobalOddRootShortQ_actual, generatedAxisGlobalOddOtherSparseShortQ_root04]
      rfl
    · rw [generatedAxisGlobalOddRoot04FastTensorState_actual,
        generatedAxisGlobalTensorFactor_rational]
      rfl

/-- Every positive transition coefficient comes from the genuine original triality operator. -/
theorem generatedAxisGlobalOddRoot04PositiveRationalPacket_actual :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalTriality generatedAxisGlobalOddRoot04RationalPacket) :=
  generatedAxisGlobalRationalTriality_of_actual _ _ generatedAxisGlobalOddRoot04RationalPacket_actual

/-- Every negative transition coefficient uses the genuine inverse original triality operator. -/
theorem generatedAxisGlobalOddRoot04NegativeRationalPacket_actual :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalInverse generatedAxisGlobalOddRoot04RationalPacket) :=
  generatedAxisGlobalRationalInverse_actual _ _ generatedAxisGlobalOddRoot04RationalPacket_actual

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
