/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadPacket00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFastMaskPhase

/-! Actual binary transport and complete scalar phases certify the next original octad rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check 16 original binary images, full source phases and true signed coefficient equalities.
/-- Checked mask transport and full scalar phases preserve the actual preferred coefficients. -/
theorem generatedSixth_xi_octad_packet02_certificate (a : Fin 16) :
    let e : Fin 64 := ⟨32 + a.val, by omega⟩
    let x := generatedSixthXiOctadPacket00OutputAddress e
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiOctadMask 190 e) =
      generatedSixthXiOctadMask x.1 x.2 ∧
    generatedSixthXiFastMaskPhase (generatedSixthXiOctadMask 190 e) =
      generatedSixthXiOctadPacket00Phase e ∧
    nortonUIntegerSign (generatedSixthXiOctadPacket00Phase e) *
      generatedSixthFinalOctadCachedNumerator 190 e =
        generatedSixthFinalOctadCachedNumerator x.1 x.2 := by
  revert a
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
