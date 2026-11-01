/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan1Block0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan1Block1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan1Block2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan1Block3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan1Block4

/-! Concatenated bounded checks certify every original signed spin edge of word1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full original phase plan is valid; every finite edge has been kernel checked. -/
theorem generatedFifth_monomial_permutation_spin_plan_1 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 1) := by
  rw [generatedFifth_permutation_plan1_blocks]
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan1_block0
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan1_block1
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan1_block2
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan1_block3
  exact generatedFifth_permutation_plan1_block4

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
