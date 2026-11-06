/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot04Short
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthIntegerWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse

/-! Complete original real-coordinate packets for both fifth root-4 triality destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every original matrix, short, and tensor coordinate after the actual root-4 local word. -/
def generatedAxisGlobalFifthRoot04Packet : ConwayRawSpace :=
  (conwayMatrixAction (generatedAxisGlobalFifthShortSpatialWord 4)
      (Matrix.diagonal generatedAxisGlobalFifthMatrixDiagonal),
    (∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
      (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot04ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot04ShortLabel i) (1 : ℝ),
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerRootData 4).1
        (generatedAxisGlobalFifthIntegerRootData 4).2))

-- Comparing all projections of the full source normalization word needs a deeper stack.
set_option maxRecDepth 10000 in
/-- This is the entire actual Griess word image, retaining every original central phase. -/
theorem generatedAxisGlobalFifthRoot04Packet_actual :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 4) generatedFifthAxis) =
        generatedAxisGlobalFifthRoot04Packet := by
  apply Prod.ext
  · exact generatedAxisGlobalFifthShortWord_matrix 4
  · apply Prod.ext
    · rw [generatedAxisGlobalFifthShortWordFiber_encode]
      exact generatedAxisGlobalFifthRoot04Short_actual
    · exact generatedAxisGlobalFifthIntegerRoot_actual 4

/-- Every coordinate of the original positive-triality destination is fixed by the actual packet. -/
theorem generatedAxisGlobalFifthRoot04Packet_triality :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 4) generatedFifthAxis)) =
        generatedAxisGlobalRawTrialityFormula generatedAxisGlobalFifthRoot04Packet := by
  rw [generatedAxisGlobalRawTrialityFormula_actual, generatedAxisGlobalFifthRoot04Packet_actual]

/-- The actual packet determines every coordinate of the original inverse-triality destination. -/
theorem generatedAxisGlobalFifthRoot04Packet_inverse :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalFifthShortLocalWord 4) generatedFifthAxis)) =
        generatedAxisGlobalRawInverseFormula generatedAxisGlobalFifthRoot04Packet := by
  rw [generatedAxisGlobalRawInverseFormula_actual, generatedAxisGlobalFifthRoot04Packet_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
