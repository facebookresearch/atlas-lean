/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadPhaseData

/-! Exact signed original coefficient covariance for a bounded batch of genuine octad families. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check all 64 original preferred signs in 33 actual occurring families.
/-- Complete preferred phase times source numerator equals the original target numerator. -/
theorem generatedSixth_monomial_octad_numerator33 :
    ∀ r : Fin 33, ∀ e : Fin 64,
      nortonUIntegerSign (generatedSixthMonomialOctadPhase 3
        (Fin.ofNat 231 (3 * 33 + r.val)) e) *
      generatedSixthFinalOctadCachedNumerator
        (generatedSixthMonomialOctadSourceFamily 3 (Fin.ofNat 231 (3 * 33 + r.val)))
        (generatedSixthMonomialOctadSourceSign 3 (Fin.ofNat 231 (3 * 33 + r.val)) e) =
      generatedSixthFinalOctadCachedNumerator (Fin.ofNat 231 (3 * 33 + r.val)) e := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
