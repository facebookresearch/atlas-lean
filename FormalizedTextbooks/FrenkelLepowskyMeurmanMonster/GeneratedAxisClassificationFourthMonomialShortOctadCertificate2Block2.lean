/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortTargets2

/-! Bounded genuine full-phase octad checks for corrected word 2, block 2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Seven actual families retain all64 preferred signs and every original central phase.
/-- Exact full-Q and original signed-coefficient matching for seven genuine octad families. -/
theorem generatedFourth_monomial_short_octad_certificate_2_2 :
    ∀ z : Fin 7, ∀ e : Fin 64,
      let j : Fin 63 := ⟨14 + z.val, by omega⟩
      generatedFourthMonomialShortMatch 2 (generatedFourthLiftShortSourceQ j e)
        (generatedFourthLiftShortOctadNumerator j e)
          (generatedFourthMonomialShortOctadTargets2 j e) := by
  simp only [generatedFourth_lift_short_octad_q_packed,
    generatedFourth_monomial_short_match_sparse]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
