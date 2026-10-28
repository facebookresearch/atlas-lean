/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortTargets3

/-! Bounded genuine full-phase pair checks for corrected word 3, preferred sign 1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Check every increasing pair, retaining its complete preferred central coefficient.
/-- Exact full-Q and original signed-coordinate matching for every increasing physical pair. -/
theorem generatedFourth_monomial_short_pair_certificate_3_1 :
    ∀ a b : Fin 24, a < b → generatedFourthMonomialShortMatch 3
      (generatedFourthLiftShortPairQ 1 a b)
      (generatedFourthLiftShortPairNumerator 1 a b)
      (generatedFourthMonomialShortPairTargets3 1 a b) := by
  simp only [generatedFourth_monomial_short_match_sparse]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
