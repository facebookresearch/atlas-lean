/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortPackedChecks

/-! Bounded full preferred-Q and original-coefficient pair certificate for sign 0. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Check each increasing physical pair, retaining its full central and original coefficient bits.
/-- Actual preferred-Q and coefficient matching for every increasing pair of sign 0. -/
theorem generatedFourth_lift_short_pair_certificate_0 :
    ∀ a b : Fin 24, a < b → generatedFourthLiftShortFiniteMatch
      (generatedFourthLiftShortPairQ 0 a b) (generatedFourthLiftShortPairNumerator 0 a b)
        (generatedFourthLiftShortPairTargets 0 a b) := by
  simp only [generatedFourth_lift_short_finite_match_packed]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
