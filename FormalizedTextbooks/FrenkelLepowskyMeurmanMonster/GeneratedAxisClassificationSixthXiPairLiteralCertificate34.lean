/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairLiteralCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQDecidable

/-! Bounded certificates preserve actual physical labels, full Q lifts and signed coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Full base and central coordinates decide equality of the genuine extension. -/
local instance generatedSixthXiPairLiteralQDecidable34 : DecidableEq Q := generatedSixthQDecidableEq

set_option maxHeartbeats 8000000 in
-- Check 8 actual source/output vectors, all Q coordinates and true signed numerators.
/-- All components of the block 34 complete Xi short-coordinate certificates are checked. -/
theorem generatedSixth_xi_pair_literal_certificate34 : ∀ a : Fin 8,
    let j : Fin 552 := ⟨544 + a.val, by omega⟩
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
  have h : ∀ a : Fin 8,
    let j : Fin 552 := ⟨544 + a.val, by omega⟩
    generatedSixthXiShortIntegerQ (generatedSixthXiPairLiteralInputIntegral j) =
        generatedSixthXiPackedQ (generatedSixthXiPairSourceQ j) ∧
      generatedSixthXiShortIntegerQ (generatedSixthXiPairLiteralOutputIntegral j) =
        generatedSixthXiPackedQ (generatedSixthXiPairOutputQ j) ∧
      sixthFrameOrbitSpatialNumerator 14 *ᵥ generatedSixthXiPairLiteralInputIntegral j =
        (fun i => 2 * nortonUIntegerSign (generatedSixthXiPairPhysicalPhase j) *
          generatedSixthXiPairLiteralOutputIntegral j i) ∧
      generatedSixthXiPairExecutablePhase j = generatedSixthXiPairPhase j ∧
      nortonUIntegerSign (generatedSixthXiPairPhase j) *
                generatedSixthXiPairInputNumerator j = generatedSixthXiPairOutputNumerator j := by
    decide +kernel
  have hi : ∀ j, generatedSixthXiPairLiteralInputIntegral j =
      generatedSixthXiPairInputIntegral j := fun j =>
    funext (generatedSixth_xi_pair_literal_input j)
  have ho : ∀ j, generatedSixthXiPairLiteralOutputIntegral j =
      generatedSixthXiPairOutputIntegral j := fun j =>
    funext (generatedSixth_xi_pair_literal_output j)
  simpa only [hi, ho] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
