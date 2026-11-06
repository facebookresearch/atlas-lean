/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftIntegerOperators

/-! Actual preferred-Q conjugation by the genuine extraspecial-corrected flag lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The full original corrected conjugation, including every actual central coefficient. -/
noncomputable def generatedFourthLiftCorrectedQImage (q : Q) : Q :=
  generatedFourthFlagXiCorrection * generatedFourthFlagNormalizedQImage q *
    generatedFourthFlagXiCorrection⁻¹

/-- The finite expression is the actual spin conjugation by the corrected local lift. -/
theorem generatedFourth_lift_corrected_q_image (q : Q) :
    spinConjugation generatedFourthFlagCorrectedLift.val.1 q =
      generatedFourthLiftCorrectedQImage q := by
  change spinConjugation (spinHolomorphIncl generatedFourthFlagXiCorrection *
    generatedFourthFlagNormalizedLift.val.1) q = _
  rw [map_mul]
  change spinConjugation (spinHolomorphIncl generatedFourthFlagXiCorrection)
    (spinConjugation generatedFourthFlagNormalizedLift.val.1 q) = _
  rw [generatedFourth_flag_lift_conjugation, spinConjugation_incl]
  rfl

set_option maxHeartbeats 8000000 in
-- Retain the original Parker and grey Gaussian phases at one actual preferred octad coordinate.
/-- A bounded actual preferred-Q check for the first selected octad sign. -/
theorem generatedFourth_lift_short_first_image :
    generatedFourthLiftCorrectedQImage (generatedFourthLiftShortSourceQ 0 0) =
      generatedFourthLiftShortSourceQ 0 33 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    decide +kernel
  · apply Multiplicative.toAdd.injective
    decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
