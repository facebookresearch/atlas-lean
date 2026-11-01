/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanDecidable

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Every step of the plan is a bounded binary matrix and phase check.
/-- Every coordinate and Parker-phase edge of root-two plan 4 is checked. -/
theorem generatedFeasibleAmbientTenth_monomial_plan_check04 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel representativeSpinIdentityModel
      generatedFeasibleAmbientTenthMonomialPlan04 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
