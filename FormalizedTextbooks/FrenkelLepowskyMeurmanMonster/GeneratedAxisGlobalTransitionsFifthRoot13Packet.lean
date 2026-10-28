/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot13Short
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthIntegerWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse

/-! Complete original real-coordinate packets for both fifth root-13 triality destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every original matrix, short, and tensor coordinate after the actual root-13 local word. -/
def generatedAxisGlobalFifthRoot13Packet : ConwayRawSpace :=
  (conwayMatrixAction (generatedAxisGlobalFifthShortSpatialWord 13)
      (Matrix.diagonal generatedAxisGlobalFifthMatrixDiagonal),
    (∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
      (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot13ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot13ShortLabel i) (1 : ℝ),
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerRootData 13).1
        (generatedAxisGlobalFifthIntegerRootData 13).2))

-- Comparing all projections of the full source normalization word needs a deeper stack.
set_option maxRecDepth 10000 in
/-- This is the entire actual Griess word image, retaining every original central phase. -/
theorem generatedAxisGlobalFifthRoot13Packet_actual :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 13) generatedFifthAxis) =
        generatedAxisGlobalFifthRoot13Packet := by
  apply Prod.ext
  · exact generatedAxisGlobalFifthShortWord_matrix 13
  · apply Prod.ext
    · rw [generatedAxisGlobalFifthShortWordFiber_encode]
      exact generatedAxisGlobalFifthRoot13Short_actual
    · exact generatedAxisGlobalFifthIntegerRoot_actual 13

/-- Every coordinate of the original positive-triality destination is fixed by the actual packet. -/
theorem generatedAxisGlobalFifthRoot13Packet_triality :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 13) generatedFifthAxis)) =
        generatedAxisGlobalRawTrialityFormula generatedAxisGlobalFifthRoot13Packet := by
  rw [generatedAxisGlobalRawTrialityFormula_actual, generatedAxisGlobalFifthRoot13Packet_actual]

/-- The actual packet determines every coordinate of the original inverse-triality destination. -/
theorem generatedAxisGlobalFifthRoot13Packet_inverse :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalFifthShortLocalWord 13) generatedFifthAxis)) =
        generatedAxisGlobalRawInverseFormula generatedAxisGlobalFifthRoot13Packet := by
  rw [generatedAxisGlobalRawInverseFormula_actual, generatedAxisGlobalFifthRoot13Packet_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
