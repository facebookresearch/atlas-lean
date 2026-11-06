/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortPackedChecks

/-! Bounded full preferred-Q and original-coefficient octad certificate block 2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Seven actual code families retain all sixty-four original signs and their full central phases.
/-- Actual preferred-Q and coefficient matching for listed octad rows 14 through 20. -/
theorem generatedFourth_lift_short_octad_certificate_2 :
    ∀ k : Fin 7, ∀ e : Fin 64,
      let j : Fin 63 := ⟨14 + k.val, by omega⟩
      generatedFourthLiftShortFiniteMatch (generatedFourthLiftShortSourceQ j e)
        (generatedFourthLiftShortOctadNumerator j e)
          (generatedFourthLiftShortOctadTargets j e) := by
  simp only [generatedFourth_lift_short_octad_q_packed,
    generatedFourth_lift_short_finite_match_packed]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
