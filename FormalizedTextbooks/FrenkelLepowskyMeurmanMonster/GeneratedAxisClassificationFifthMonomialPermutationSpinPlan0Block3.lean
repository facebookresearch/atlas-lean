/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan0Blocks

/-! Check at most eight original full-phase monomial spin edges. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Verify all binary coordinate entries and complete quadratic coefficients of each edge.
/-- Bounded block3 of actual word0 has its complete original signed action. -/
theorem generatedFifth_permutation_plan0_block3 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel
      generatedFifthPermutationPlan0Input3 generatedFifthPermutationPlan0Block3 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
