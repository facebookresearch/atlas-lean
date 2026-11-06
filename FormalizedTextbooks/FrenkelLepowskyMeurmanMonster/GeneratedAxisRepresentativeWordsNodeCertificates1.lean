/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded kernel certificates of complete spin coordinate and sign actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanDecidable

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 5 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate5 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (5 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 6 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate6 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (6 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 7 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate7 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (7 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 8 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate8 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (8 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 9 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate9 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (9 : Fin 15)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
