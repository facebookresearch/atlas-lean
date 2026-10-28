/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFastChecks

/-! A bounded replay of actual short matching with certified theta evaluation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check full preferred-Q images and original integer coefficients after exact theta caching.
/-- Every first-family short coordinate passes the original certificate with cached evaluation. -/
theorem generatedFourth_lift_short_theta_profile :
    ∀ e : Fin 64, generatedFourthLiftShortFiniteMatch
      (generatedFourthLiftShortSourceQ 0 e) (generatedFourthLiftShortOctadNumerator 0 e)
        (generatedFourthLiftShortOctadTargets 0 e) := by
  simp only [generatedFourth_lift_short_octad_q_fast, generatedFourth_lift_short_finite_match_fast]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
