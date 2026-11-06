/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanDecidable

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
/-- Every coordinate and full quadratic phase edge of the original permutation word is checked. -/
theorem generatedAxisGlobalComparisonMonomialPlan_check05 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel representativeSpinIdentityModel
      generatedAxisGlobalComparisonMonomialPlan05 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
