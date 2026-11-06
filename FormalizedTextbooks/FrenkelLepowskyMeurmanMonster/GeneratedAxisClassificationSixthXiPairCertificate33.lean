/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairScalarCertificate33

/-! Reuse the checked original pair-source block 33. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- All components of the block 33 complete Xi short-coordinate certificates are checked. -/
theorem generatedSixth_xi_pair_certificate33 : ∀ a : Fin 16,
    let j : Fin 552 := ⟨528 + a.val, by omega⟩
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
  generatedSixth_xi_pair_scalar_certificate33

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
