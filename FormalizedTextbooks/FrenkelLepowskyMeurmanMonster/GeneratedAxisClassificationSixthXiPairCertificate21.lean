/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQDecidable
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairLiteralCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairScalarCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiMatrixPhase

/-! Bounded certificates preserve actual physical labels, full Q lifts and signed coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Full base and central coordinates decide equality of the genuine extension. -/
local instance generatedSixthXiPairQDecidable21 : DecidableEq Q := generatedSixthQDecidableEq

set_option maxHeartbeats 8000000 in
-- Check 16 actual source/output vectors, all Q coordinates and true signed numerators.
/-- All components of the block 21 complete Xi short-coordinate certificates are checked. -/
theorem generatedSixth_xi_pair_certificate21 : ∀ a : Fin 16,
    let j : Fin 552 := ⟨336 + a.val, by omega⟩
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
  have h : ∀ a : Fin 16,
    let j : Fin 552 := ⟨336 + a.val, by omega⟩
    generatedSixthXiShortIntegerQ (generatedSixthXiPairLiteralInputIntegral j) =
        generatedSixthXiPackedQ (generatedSixthXiPairScalarSourceQ j) ∧
      generatedSixthXiShortIntegerQ (generatedSixthXiPairLiteralOutputIntegral j) =
        generatedSixthXiPackedQ (generatedSixthXiPairScalarOutputQ j) ∧
      sixthFrameOrbitSpatialNumerator 14 *ᵥ generatedSixthXiPairLiteralInputIntegral j =
        (fun i => 2 * nortonUIntegerSign (generatedSixthXiPairPhysicalPhase j) *
          generatedSixthXiPairLiteralOutputIntegral j i) ∧
      generatedSixthXiMatrixPhase
        (golayLabelCoefficients (generatedSixthXiPairScalarSourceQ j).1)
        (golayLabelCoefficients (generatedSixthXiPairScalarSourceQ j).2)
        (golayLabelCoefficients (generatedSixthXiPairScalarOutputQ j).1)
        (golayLabelCoefficients (generatedSixthXiPairScalarOutputQ j).2) =
          generatedSixthXiPairScalarPhase j ∧
      nortonUIntegerSign (generatedSixthXiPairScalarPhase j) *
                generatedSixthXiPairScalarInputNumerator j =
          generatedSixthXiPairScalarOutputNumerator j := by
    decide +kernel
  have hi : ∀ j, generatedSixthXiPairLiteralInputIntegral j =
      generatedSixthXiPairInputIntegral j := fun j =>
    funext (generatedSixth_xi_pair_literal_input j)
  have ho : ∀ j, generatedSixthXiPairLiteralOutputIntegral j =
      generatedSixthXiPairOutputIntegral j := fun j =>
    funext (generatedSixth_xi_pair_literal_output j)
  simpa only [hi, ho, generatedSixth_xi_pair_matrix_phase,
    ← generatedSixth_xi_pair_scalar_source_Q, ← generatedSixth_xi_pair_scalar_output_Q,
    ← generatedSixth_xi_pair_scalar_phase, ← generatedSixth_xi_pair_scalar_input_numerator,
    ← generatedSixth_xi_pair_scalar_output_numerator] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
