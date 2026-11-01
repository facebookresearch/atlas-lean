/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinateTransitionReturns

/-! Complete original encoder certificate for the old incident coordinate octads. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Actual original twelve-bit octad codes containing physical coordinates eight and nine. -/
def generatedFeasibleContainingCoordinateIncidentCodes : Finset (Fin 4096) :=
  golayOctads.filter (fun d => (golayEncodedMask d.val).testBit 8 = true ∧
    (golayEncodedMask d.val).testBit 9 = true)

set_option maxHeartbeats 40000000 in
-- This bounded kernel gate checks the original4096 encoder labels and both physical bits.
/-- Exactly77 original octads contain both coordinates of the old incident root. -/
theorem generatedFeasibleContainingCoordinateIncidentCodes_card :
    generatedFeasibleContainingCoordinateIncidentCodes.card = 77 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
