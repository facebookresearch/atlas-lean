/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Block0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Block1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Block2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Block3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Block4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Block5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Block6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan3Block7

/-! Concatenated bounded checks certify every original signed spin edge of word3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full original phase plan is valid; every finite edge has been kernel checked. -/
theorem generatedFifth_monomial_permutation_spin_plan_3 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 3) := by
  rw [generatedFifth_permutation_plan3_blocks]
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan3_block0
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan3_block1
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan3_block2
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan3_block3
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan3_block4
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan3_block5
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan3_block6
  exact generatedFifth_permutation_plan3_block7

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
