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
/-- The full spin plan for node 0 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate0 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (0 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 1 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate1 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (1 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 2 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate2 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (2 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 3 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate3 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (3 : Fin 15)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for node 4 is kernel checked. -/
theorem representativeNodeSpin_plan_certificate4 :
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan (4 : Fin 15)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
