/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadPacket00Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator

/-! Complete original physical and signed coefficient checks fix the first octad outputs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each checked octad source yields genuine fixation at its original preferred output label. -/
theorem generatedSixth_xi_octad_packet00_fixed (a : Fin 16) :
    let e : Fin 64 := ⟨a.val, by omega⟩
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1
        (generatedSixthXiOctadPacket00Output e) =
      (griessConwayEncode generatedSixthAxis).2.1
        (generatedSixthXiOctadPacket00Output e) := by
  let e : Fin 64 := ⟨a.val, by omega⟩
  have h := generatedSixth_xi_octad_packet00_certificate a
  change localShortOperator (generatedSixthCorrectedGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.1
      (generatedSixthXiOctadPacket00Output e) = _
  have hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2
      (generatedSixthXiOctadPacket00Input e) = generatedSixthXiOctadPacket00Output e := by
    apply generatedSixth_xi_short_permutation_of_integer _ _
      (generatedSixthXiOctadPacket00PhysicalPhase e)
    rw [generatedSixth_xi_octad_packet00_input_integral,
      generatedSixth_xi_octad_packet00_output_integral]
    exact h.2.1
  rw [generatedSixth_xi_short_selected_operator _ _ hs,
    generatedSixth_xi_short_integer_Q _ _
      (generatedSixth_xi_octad_packet00_input_integral e), h.1, h.2.2.1]
  apply generatedSixth_final_short_signed
  simpa only [generatedSixthFinalShortNumerator, generatedSixthXiOctadPacket00Input,
    generatedSixthXiOctadPacket00Output, generatedSixth_final_octad_cache_label,
    ← generatedSixth_final_octad_cached_numerator] using h.2.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
