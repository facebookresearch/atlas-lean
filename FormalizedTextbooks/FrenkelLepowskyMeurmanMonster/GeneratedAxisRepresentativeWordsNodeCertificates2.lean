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
/-- The full spin plan for node 10 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate10 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (10 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 11 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate11 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (11 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 12 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate12 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (12 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 13 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate13 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (13 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 14 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate14 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (14 : Fin 15)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
