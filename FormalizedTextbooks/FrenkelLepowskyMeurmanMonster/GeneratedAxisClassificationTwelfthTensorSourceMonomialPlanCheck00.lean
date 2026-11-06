/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanDecidable

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
/-- Bounded binary matrices certify every full original Parker-phase edge. -/
theorem generatedTwelfth_tensor_source_monomial_plan_check00 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel representativeSpinIdentityModel
      generatedTwelfthTensorSourceMonomialPlan00 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
