/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerOddFourthPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthFastFrameTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthPhysicalOutgoingTensor

/-! Kernel checks for every term of a bounded original pairing packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 20000
-- Normalize only the complete bounded packet of original exact rational coefficients.
set_option maxHeartbeats 1000000000

/-- Every complete original packet has its exact canonical pairing value. -/
theorem generatedAxisGlobalOddFourthMiddlePairingPartCheck00Odd03 :
    generatedAxisGlobalOddFourthMiddleOddPairingPart 0 3 = 8 := by
  rw [generatedAxisGlobalIntegerOddFourthOddPairingPart_rat]
  have hz : generatedAxisGlobalIntegerOddFourthOddPairingPart 0 3 = 8192 := by
    decide +kernel
  rw [hz]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
