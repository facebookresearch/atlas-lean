/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQDecidable

/-! Bounded certificates preserve actual physical labels, full Q lifts and signed coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Full base and central coordinates decide equality of the genuine extension. -/
local instance generatedSixthXiPairQDecidable15 : DecidableEq Q := generatedSixthQDecidableEq

set_option maxHeartbeats 8000000 in
-- Check 16 actual source/output vectors, all Q coordinates and true signed numerators.
/-- All components of the block 15 complete Xi short-coordinate certificates are checked. -/
theorem generatedSixth_xi_pair_certificate15 : ∀ a : Fin 16,
    let j : Fin 552 := ⟨240 + a.val, by omega⟩
    generatedSixthXiShortIntegerQ (generatedSixthXiPairInputIntegral j) =
        generatedSixthXiPackedQ (generatedSixthXiPairSourceQ j) ∧
      generatedSixthXiShortIntegerQ (generatedSixthXiPairOutputIntegral j) =
        generatedSixthXiPackedQ (generatedSixthXiPairOutputQ j) ∧
      sixthFrameOrbitSpatialNumerator 14 *ᵥ generatedSixthXiPairInputIntegral j =
        (fun i => 2 * nortonUIntegerSign (generatedSixthXiPairPhysicalPhase j) *
          generatedSixthXiPairOutputIntegral j i) ∧
      generatedSixthXiPairExecutablePhase j = generatedSixthXiPairPhase j ∧
      nortonUIntegerSign (generatedSixthXiPairPhase j) *
                generatedSixthXiPairInputNumerator j = generatedSixthXiPairOutputNumerator j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
