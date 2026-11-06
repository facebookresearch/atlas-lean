/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort0Assembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorFixed0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort1Assembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorFixed1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Assembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorFixed2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort3Assembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorFixed3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort4Assembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorFixed4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort5Assembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorFixed5

/-! The six original corrected monomial words fix the entire genuine fifth axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every original signed matrix plan is fully certified in the Lean kernel. -/
theorem generatedFifth_monomial_permutation_spin_plans (k : Fin 6) :
    representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan k) := by
  fin_cases k
  · exact generatedFifth_monomial_permutation_spin_plan_0
  · exact generatedFifth_monomial_permutation_spin_plan_1
  · exact generatedFifth_monomial_permutation_spin_plan_2
  · exact generatedFifth_monomial_permutation_spin_plan_3
  · exact generatedFifth_monomial_permutation_spin_plan_4
  · exact generatedFifth_monomial_permutation_spin_plan_5

/-- Every genuine short block is fixed with its original preferred-Q phases. -/
theorem generatedFifth_monomial_permutation_short_fixed (k : Fin 6) :
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.1 =
        (griessConwayEncode generatedFifthAxis).2.1 := by
  fin_cases k
  · exact generatedFifth_monomial_permutation_short_fixed_0
      generatedFifth_monomial_permutation_spin_plan_0
  · exact generatedFifth_monomial_permutation_short_fixed_1
      generatedFifth_monomial_permutation_spin_plan_1
  · exact generatedFifth_monomial_permutation_short_fixed_2
      generatedFifth_monomial_permutation_spin_plan_2
  · exact generatedFifth_monomial_permutation_short_fixed_3
      generatedFifth_monomial_permutation_spin_plan_3
  · exact generatedFifth_monomial_permutation_short_fixed_4
      generatedFifth_monomial_permutation_spin_plan_4
  · exact generatedFifth_monomial_permutation_short_fixed_5
      generatedFifth_monomial_permutation_spin_plan_5

/-- All original tensor coordinates are fixed with the full correcting Pauli signs. -/
theorem generatedFifth_monomial_permutation_tensor_fixed (k : Fin 6) :
    localTensorRepresentation (generatedFifthMonomialPermutationCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2 := by
  fin_cases k
  · exact generatedFifth_monomial_permutation_tensor_fixed_0
  · exact generatedFifth_monomial_permutation_tensor_fixed_1
  · exact generatedFifth_monomial_permutation_tensor_fixed_2
  · exact generatedFifth_monomial_permutation_tensor_fixed_3
  · exact generatedFifth_monomial_permutation_tensor_fixed_4
  · exact generatedFifth_monomial_permutation_tensor_fixed_5

/-- Each displayed corrected original monomial fiber fixes the full original fifth axis. -/
theorem generatedFifth_monomial_permutation_full_fixed (k : Fin 6) :
    rhoLocal (localFiberIntoH (generatedFifthMonomialPermutationCorrectedFiber k))
      generatedFifthAxis = generatedFifthAxis :=
  generatedFifth_monomial_permutation_full_fixed_of_blocks k
    (generatedFifth_monomial_permutation_short_fixed k)
    (generatedFifth_monomial_permutation_tensor_fixed k)

/-- These full-axis lifts project to precisely the six original spatial permutation words. -/
theorem generatedFifth_monomial_permutation_corrected_projection (k : Fin 6) :
    projH (localFiberIntoH (generatedFifthMonomialPermutationCorrectedFiber k)) =
      (QuotientGroup.mk' signsSubgroup
        (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation k)) : Co1) := by
  change QuotientGroup.mk' signsSubgroup
    (generatedFifthMonomialPermutationCorrectedFiber k).val.2 = _
  rw [generatedFifth_monomial_permutation_corrected_spatial, generatedFifth_monomial_spatial]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
