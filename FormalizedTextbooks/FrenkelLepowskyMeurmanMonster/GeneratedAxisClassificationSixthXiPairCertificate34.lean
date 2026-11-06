/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairLiteralCertificate34

/-! Reuse the checked final eight original pair-source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- All components of the block 34 complete Xi short-coordinate certificates are checked. -/
theorem generatedSixth_xi_pair_certificate34 : ∀ a : Fin 8,
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
                generatedSixthXiPairInputNumerator j = generatedSixthXiPairOutputNumerator j :=
  generatedSixth_xi_pair_literal_certificate34

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
