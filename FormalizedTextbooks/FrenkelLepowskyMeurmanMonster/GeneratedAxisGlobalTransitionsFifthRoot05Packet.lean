/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot05Short
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthIntegerWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse

/-! Complete original real-coordinate packets for both fifth root-5 triality destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every original matrix, short, and tensor coordinate after the actual root-5 local word. -/
def generatedAxisGlobalFifthRoot05Packet : ConwayRawSpace :=
  (conwayMatrixAction (generatedAxisGlobalFifthShortSpatialWord 5)
      (Matrix.diagonal generatedAxisGlobalFifthMatrixDiagonal),
    (∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
      (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot05ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot05ShortLabel i) (1 : ℝ),
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerRootData 5).1
        (generatedAxisGlobalFifthIntegerRootData 5).2))

-- Comparing all projections of the full source normalization word needs a deeper stack.
set_option maxRecDepth 10000 in
/-- This is the entire actual Griess word image, retaining every original central phase. -/
theorem generatedAxisGlobalFifthRoot05Packet_actual :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis) =
        generatedAxisGlobalFifthRoot05Packet := by
  apply Prod.ext
  · exact generatedAxisGlobalFifthShortWord_matrix 5
  · apply Prod.ext
    · rw [generatedAxisGlobalFifthShortWordFiber_encode]
      exact generatedAxisGlobalFifthRoot05Short_actual
    · exact generatedAxisGlobalFifthIntegerRoot_actual 5

/-- Every coordinate of the original positive-triality destination is fixed by the actual packet. -/
theorem generatedAxisGlobalFifthRoot05Packet_triality :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis)) =
        generatedAxisGlobalRawTrialityFormula generatedAxisGlobalFifthRoot05Packet := by
  rw [generatedAxisGlobalRawTrialityFormula_actual, generatedAxisGlobalFifthRoot05Packet_actual]

/-- The actual packet determines every coordinate of the original inverse-triality destination. -/
theorem generatedAxisGlobalFifthRoot05Packet_inverse :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis)) =
        generatedAxisGlobalRawInverseFormula generatedAxisGlobalFifthRoot05Packet := by
  rw [generatedAxisGlobalRawInverseFormula_actual, generatedAxisGlobalFifthRoot05Packet_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
