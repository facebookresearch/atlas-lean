/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanCheck04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthCompactFrameTensor

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original full signed permutation plan required for the four Fourth frames is verified. -/
theorem generatedAxisGlobalOddFourthCompactFrame_plans (j : Fin 5) :
    representativeSpinPlanValid generatedFourthMonomialLetterModel representativeSpinIdentityModel
      (generatedAxisGlobalComparisonMonomialPlan (Fin.castAdd 3 j)) := by
  fin_cases j
  · exact generatedAxisGlobalComparisonMonomialPlan_check00
  · exact generatedAxisGlobalComparisonMonomialPlan_check01
  · exact generatedAxisGlobalComparisonMonomialPlan_check02
  · exact generatedAxisGlobalComparisonMonomialPlan_check03
  · exact generatedAxisGlobalComparisonMonomialPlan_check04

/-- All physical tensor coordinates of all four complete original frames use their checked compact formulas. -/
theorem generatedAxisGlobalOddFourthCompactFrameTensor_unconditional (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddFourthComparisonFiber k)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFourthCompactFrameTensor k T) :=
  generatedAxisGlobalOddFourthCompactFrameTensor_actual k
    generatedAxisGlobalOddFourthCompactFrame_plans T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
