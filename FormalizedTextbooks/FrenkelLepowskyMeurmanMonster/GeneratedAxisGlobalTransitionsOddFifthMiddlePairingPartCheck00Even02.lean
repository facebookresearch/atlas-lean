/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingParts

/-! Every coefficient of the bounded original finite pairing packet is kernel checked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxRecDepth 20000
-- Evaluate only this bounded complete packet of original exact rational coefficients.
set_option maxHeartbeats 1000000000

/-- The whole original packet has its exact canonical pairing value. -/
theorem generatedAxisGlobalOddFifthMiddlePairingPartCheck00Even02 :
    generatedAxisGlobalOddFifthMiddleEvenPairingPart 0 2 = 8 := by
  unfold generatedAxisGlobalOddFifthMiddleEvenPairingPart
    generatedAxisGlobalOddFifthMiddleShortBitQ generatedAxisGlobalOddFifthMiddleShortFastQ
  simp_rw [← generatedAxisGlobalOddFifthSparseSelectedShortQ_eq]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
