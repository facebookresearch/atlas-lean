/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadData

/-! Exact support transport of every occurring original octad under the literal input array. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check all 231 source supports against all 24 original physical coordinates.
/-- The displayed source code support pulls back to the genuine target support. -/
theorem generatedSixth_monomial_octad_support2 :
    ∀ f : Fin 231, ∀ i : Fin 24,
    (generatedSixthMonomialOctadSupportMask (generatedSixthMonomialOctadSourceFamily 2 f)).testBit
      (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 (2 : Fin 4))) i).val =
        (generatedSixthMonomialOctadSupportMask f).testBit i.val := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
