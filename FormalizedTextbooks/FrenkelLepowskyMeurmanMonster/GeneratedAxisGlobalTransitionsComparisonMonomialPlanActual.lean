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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanCheck05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanCheck06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanCheck07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanSoundness

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All full signed coordinate/phase edges have unconditional original kernel certificates. -/
theorem generatedAxisGlobalComparisonMonomialPlans_valid (k : Fin 8) :
    representativeSpinPlanValid generatedFourthMonomialLetterModel representativeSpinIdentityModel
      (generatedAxisGlobalComparisonMonomialPlan k) := by
  fin_cases k
  · exact generatedAxisGlobalComparisonMonomialPlan_check00
  · exact generatedAxisGlobalComparisonMonomialPlan_check01
  · exact generatedAxisGlobalComparisonMonomialPlan_check02
  · exact generatedAxisGlobalComparisonMonomialPlan_check03
  · exact generatedAxisGlobalComparisonMonomialPlan_check04
  · exact generatedAxisGlobalComparisonMonomialPlan_check05
  · exact generatedAxisGlobalComparisonMonomialPlan_check06
  · exact generatedAxisGlobalComparisonMonomialPlan_check07

/-- Every compact tensor formula is the complete actual original frame permutation action. -/
theorem generatedAxisGlobalComparisonMonomialTensor_unconditional (k : Fin 8)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (((generatedAxisGlobalComparisonMonomialWord k).map
      generatedFourthMonomialFiberLetter).prod) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalComparisonMonomialTensor k T) :=
  generatedAxisGlobalComparisonMonomialTensor_actual k
    (generatedAxisGlobalComparisonMonomialPlans_valid k) T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
