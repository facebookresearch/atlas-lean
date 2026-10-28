/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanDecidable

/-! Finite signed matrix-product checks for original monomial word 0. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Check only the literal12 by12 coordinate and phase coefficients at each short word edge.
/-- Every intermediate matrix model of this original word passes the full signed edge check. -/
theorem generatedFourth_monomial_spin_plan_certificate_0 :
    representativeSpinPlanValid generatedFourthMonomialLetterModel representativeSpinIdentityModel
      generatedFourthMonomialSpinPlan0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
