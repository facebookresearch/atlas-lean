/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSourceCoordinates

/-! Exact preferred global sign normalization in the original octad dictionary. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check 33 actual families, all 64 signs and all eight local positions.
/-- The normalized source signs equal the original target signs up to one global sign. -/
theorem generatedSixth_monomial_octad_sign13 :
    ∀ r : Fin 33, ∀ e : Fin 64, ∀ a : Fin 8,
      (if (trialityEvenMask (generatedSixthMonomialOctadSourceSign 1
        (Fin.ofNat 231 (3 * 33 + r.val)) e)).testBit
          (generatedSixthMonomialOctadSourceCoordinate 1
            (Fin.ofNat 231 (3 * 33 + r.val)) a).val then (-1 : ℤ) else 1) =
      generatedSixthMonomialOctadPhysicalSign 1 (Fin.ofNat 231 (3 * 33 + r.val)) e *
        (if (trialityEvenMask e).testBit a.val then (-1 : ℤ) else 1) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
