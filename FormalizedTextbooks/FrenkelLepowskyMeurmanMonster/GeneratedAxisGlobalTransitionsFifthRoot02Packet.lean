/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot02Short
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthIntegerWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse

/-! Complete original real-coordinate packets for both fifth root-2 triality destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every original matrix, short, and tensor coordinate after the actual root-2 local word. -/
def generatedAxisGlobalFifthRoot02Packet : ConwayRawSpace :=
  (conwayMatrixAction (generatedAxisGlobalFifthShortSpatialWord 2)
      (Matrix.diagonal generatedAxisGlobalFifthMatrixDiagonal),
    (∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
      (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot02ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot02ShortLabel i) (1 : ℝ),
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerRootData 2).1
        (generatedAxisGlobalFifthIntegerRootData 2).2))

-- Comparing all projections of the full source normalization word needs a deeper stack.
set_option maxRecDepth 10000 in
/-- This is the entire actual Griess word image, retaining every original central phase. -/
theorem generatedAxisGlobalFifthRoot02Packet_actual :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 2) generatedFifthAxis) =
        generatedAxisGlobalFifthRoot02Packet := by
  apply Prod.ext
  · exact generatedAxisGlobalFifthShortWord_matrix 2
  · apply Prod.ext
    · rw [generatedAxisGlobalFifthShortWordFiber_encode]
      exact generatedAxisGlobalFifthRoot02Short_actual
    · exact generatedAxisGlobalFifthIntegerRoot_actual 2

/-- Every coordinate of the original positive-triality destination is fixed by the actual packet. -/
theorem generatedAxisGlobalFifthRoot02Packet_triality :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 2) generatedFifthAxis)) =
        generatedAxisGlobalRawTrialityFormula generatedAxisGlobalFifthRoot02Packet := by
  rw [generatedAxisGlobalRawTrialityFormula_actual, generatedAxisGlobalFifthRoot02Packet_actual]

/-- The actual packet determines every coordinate of the original inverse-triality destination. -/
theorem generatedAxisGlobalFifthRoot02Packet_inverse :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalFifthShortLocalWord 2) generatedFifthAxis)) =
        generatedAxisGlobalRawInverseFormula generatedAxisGlobalFifthRoot02Packet := by
  rw [generatedAxisGlobalRawInverseFormula_actual, generatedAxisGlobalFifthRoot02Packet_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
