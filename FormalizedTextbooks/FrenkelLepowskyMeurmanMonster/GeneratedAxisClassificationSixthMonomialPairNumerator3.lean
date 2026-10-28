/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairData

/-! The complete signed cleared coefficient is checked on every physical pair. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check all preferred pair signs and distinct target coordinates with original code bits.
/-- The original signed numerator is preserved on every actual target pair. -/
theorem generatedSixth_monomial_pair_numerator3 :
    ∀ s : Fin 2, ∀ a b : Fin 24, a < b →
      nortonUIntegerSign (generatedSixthMonomialPairPhase 3 a b) *
        generatedSixthMonomialPairNumerator s (generatedSixthMonomialPairInput 3 a)
          (generatedSixthMonomialPairInput 3 b) =
        generatedSixthMonomialPairNumerator s a b := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
