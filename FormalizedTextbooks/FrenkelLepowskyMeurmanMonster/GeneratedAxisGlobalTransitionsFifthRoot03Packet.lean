/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot03Short
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthIntegerWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse

/-! Complete original real-coordinate packets for both fifth root-3 triality destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every original matrix, short, and tensor coordinate after the actual root-3 local word. -/
def generatedAxisGlobalFifthRoot03Packet : ConwayRawSpace :=
  (conwayMatrixAction (generatedAxisGlobalFifthShortSpatialWord 3)
      (Matrix.diagonal generatedAxisGlobalFifthMatrixDiagonal),
    (∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
      (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot03ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot03ShortLabel i) (1 : ℝ),
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerRootData 3).1
        (generatedAxisGlobalFifthIntegerRootData 3).2))

-- Comparing all projections of the full source normalization word needs a deeper stack.
set_option maxRecDepth 10000 in
/-- This is the entire actual Griess word image, retaining every original central phase. -/
theorem generatedAxisGlobalFifthRoot03Packet_actual :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 3) generatedFifthAxis) =
        generatedAxisGlobalFifthRoot03Packet := by
  apply Prod.ext
  · exact generatedAxisGlobalFifthShortWord_matrix 3
  · apply Prod.ext
    · rw [generatedAxisGlobalFifthShortWordFiber_encode]
      exact generatedAxisGlobalFifthRoot03Short_actual
    · exact generatedAxisGlobalFifthIntegerRoot_actual 3

/-- Every coordinate of the original positive-triality destination is fixed by the actual packet. -/
theorem generatedAxisGlobalFifthRoot03Packet_triality :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 3) generatedFifthAxis)) =
        generatedAxisGlobalRawTrialityFormula generatedAxisGlobalFifthRoot03Packet := by
  rw [generatedAxisGlobalRawTrialityFormula_actual, generatedAxisGlobalFifthRoot03Packet_actual]

/-- The actual packet determines every coordinate of the original inverse-triality destination. -/
theorem generatedAxisGlobalFifthRoot03Packet_inverse :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalFifthShortLocalWord 3) generatedFifthAxis)) =
        generatedAxisGlobalRawInverseFormula generatedAxisGlobalFifthRoot03Packet := by
  rw [generatedAxisGlobalRawInverseFormula_actual, generatedAxisGlobalFifthRoot03Packet_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
