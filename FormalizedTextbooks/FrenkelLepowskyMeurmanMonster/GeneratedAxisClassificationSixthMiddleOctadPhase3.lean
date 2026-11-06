/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadSource

/-! Bounded preferred-Q phase and normalized coefficient certificate for octad batch 3. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check the original full-Q basis formula, independently of physical vector signs.
/-- Every batch-3 phase and coefficient numerator equals its actual original formula. -/
theorem generatedSixth_middle_octad_phase_weight_certificate3 : ∀ k : Fin 39,
    let n : Fin 273 := ⟨117 + k.val, by omega⟩
    Multiplicative.toAdd (generatedSixthPairQImage (generatedSixthMiddleOctadInput n).1
      (griessPairSyndrome (generatedSixthMiddleOctadInput n).2)).coeff =
        generatedSixthMiddleOctadPhase n ∧
      (if generatedSixthMiddleOctadPhase n = 0 then
        generatedSixthSourceShortWeight (generatedSixthMiddleOctadInput n) else
        -generatedSixthSourceShortWeight (generatedSixthMiddleOctadInput n)) =
          generatedSixthMiddleOctadWeight n := by
  intro k
  dsimp only
  rw [generatedSixth_middle_octad_input_syndrome, generatedSixth_middle_octad_input_weight]
  dsimp only [generatedSixthMiddleOctadInput]
  revert k
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
