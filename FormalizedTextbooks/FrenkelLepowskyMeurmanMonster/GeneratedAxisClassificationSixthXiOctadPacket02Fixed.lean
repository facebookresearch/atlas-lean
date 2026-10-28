/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadPacket02Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortMaskFixed

/-! Exact preferred masks and original signed numerators give actual octad-coordinate fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each checked mask transports its original preferred octad coefficient with its full sign. -/
theorem generatedSixth_xi_octad_packet02_fixed (a : Fin 16) :
    let e : Fin 64 := ⟨32 + a.val, by omega⟩
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1
        (generatedSixthXiOctadPacket00Output e) =
      (griessConwayEncode generatedSixthAxis).2.1
        (generatedSixthXiOctadPacket00Output e) := by
  let e : Fin 64 := ⟨32 + a.val, by omega⟩
  have h := generatedSixth_xi_octad_packet02_certificate a
  change localShortOperator (generatedSixthCorrectedGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.1
      (generatedSixthXiOctadPacket00Output e) = _
  apply generatedSixth_xi_short_fixed_of_mask_certificate
    (generatedSixthXiOctadPacket00Input e) _
    (generatedSixthXiOctadMask 190 e)
    (generatedSixthXiOctadMask (generatedSixthXiOctadPacket00OutputAddress e).1
      (generatedSixthXiOctadPacket00OutputAddress e).2)
  · exact generatedSixth_xi_octad_mask_Q 190 e
  · exact generatedSixth_xi_octad_mask_Q _ _
  · exact h.1
  · have hp := h.2.1
    rw [hp]
    simpa only [generatedSixthFinalShortNumerator, generatedSixthXiOctadPacket00Input,
      generatedSixthXiOctadPacket00Output, generatedSixth_final_octad_cache_label,
      ← generatedSixth_final_octad_cached_numerator] using h.2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
