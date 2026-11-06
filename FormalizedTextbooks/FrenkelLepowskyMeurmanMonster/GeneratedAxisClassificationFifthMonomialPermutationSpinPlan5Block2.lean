/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinMask5Block2Data

/-! Exact integer row products certify the original full signed matrix block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check finite XOR rows and all diagonal and polarized quadratic coefficient bits.
/-- Bounded block 2 of actual word 5 retains the entire original signed action. -/
theorem generatedFifth_permutation_plan5_block2 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel
      generatedFifthPermutationPlan5Input2 generatedFifthPermutationPlan5Block2 := by
  have hc : generatedFifthSpinMaskPlanCheck generatedFifthSpinMaskLetterRows
      generatedFifthPermutationMask5Input2 generatedFifthPermutationMask5Block2 := by
    decide +kernel
  have h := generatedFifth_spin_mask_plan_sound generatedFifthSpinMaskLetterRows
    generatedFourthMonomialLetterModel generatedFifth_spin_mask_letter_model
    generatedFifthPermutationMask5Input2 generatedFifthPermutationMask5Block2 hc
  rw [generatedFifth_permutation_mask5_input2, generatedFifth_permutation_mask5_block2] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
