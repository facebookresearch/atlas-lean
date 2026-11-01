/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06FastTensorStateAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadTensorZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorRationalPacket

/-! Full original source bindings give the genuine entire positive transition, with exactly zero tensor coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every matrix, short, and tensor input is the literal original root-six source action. -/
theorem generatedAxisGlobalOddRoot06SparsePacket_actual :
    griessConwayEncode (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalOddSparseRootPacket 1) := by
  apply Prod.ext
  · exact generatedAxisGlobalOddRootMatrix_actual 6
  · apply Prod.ext
    · funext r
      change (griessConwayEncode
        (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)).2.1 r =
          (generatedAxisGlobalOddSparseShortQ 1 r : ℝ)
      rw [generatedAxisGlobalOddRootShortQ_actual, generatedAxisGlobalOddSparseShortQ_root06]
    · rw [generatedAxisGlobalOddRoot06FastTensorState_actual, generatedAxisGlobalTensorFactor_rational]
      rfl

/-- The complete actual positive source transition is the full rational triality packet. -/
theorem generatedAxisGlobalOddRoot06PositivePacket_actual :
    griessConwayEncode (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalRationalTriality
        (generatedAxisGlobalOddSparseRootPacket 1)) :=
  generatedAxisGlobalRationalTriality_of_actual _ _ generatedAxisGlobalOddRoot06SparsePacket_actual

/-- Every genuine outgoing source tensor coordinate is exactly zero. -/
theorem generatedAxisGlobalOddRoot06PositiveTensor_zero :
    (griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis))).2.2 = 0 := by
  rw [generatedAxisGlobalOddRoot06PositivePacket_actual]
  funext t j
  simp only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalOddRoot06PositiveTensorQ_zero,
    Pi.zero_apply, Rat.cast_zero, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
