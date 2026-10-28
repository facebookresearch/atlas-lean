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
/-- The full spin plan for permutation 12 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate12 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (12 : Fin 83))
      (representativePermutationSpinPlan (12 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 13 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate13 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (13 : Fin 83))
      (representativePermutationSpinPlan (13 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 14 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate14 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (14 : Fin 83))
      (representativePermutationSpinPlan (14 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 15 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate15 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (15 : Fin 83))
      (representativePermutationSpinPlan (15 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 16 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate16 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (16 : Fin 83))
      (representativePermutationSpinPlan (16 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 17 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate17 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (17 : Fin 83))
      (representativePermutationSpinPlan (17 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
