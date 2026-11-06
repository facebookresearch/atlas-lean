/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingParts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthSparseOutgoingShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthCachedFramedMatrix

/-! Kernel checks for every term of a bounded original pairing packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 20000
-- Normalize only the complete bounded packet of original exact rational coefficients.
set_option maxHeartbeats 1000000000

/-- Every complete original packet has its exact canonical pairing value. -/
theorem generatedAxisGlobalOddFourthMiddlePairingPartCheck01Pair00 :
    generatedAxisGlobalOddFourthMiddlePairPairingPart 1 = 1 := by
  unfold generatedAxisGlobalOddFourthMiddlePairPairingPart
    generatedAxisGlobalOddFourthMiddleShortSparseBitQ
  simp_rw [← generatedAxisGlobalOddFourthCachedFramedMatrix_eq,
    ← generatedAxisGlobalOddFourthSparseSelectedShortQ_eq]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
