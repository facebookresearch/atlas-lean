/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Block0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Block1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Block2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Block3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Block4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Block5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan5Block6

/-! Concatenated bounded checks certify every original signed spin edge of word5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full original phase plan is valid; every finite edge has been kernel checked. -/
theorem generatedFifth_monomial_permutation_spin_plan_5 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 5) := by
  rw [generatedFifth_permutation_plan5_blocks]
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan5_block0
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan5_block1
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan5_block2
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan5_block3
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan5_block4
  apply generatedFifth_monomial_plan_valid_append _ _ _ _
    generatedFifth_permutation_plan5_block5
  exact generatedFifth_permutation_plan5_block6

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
