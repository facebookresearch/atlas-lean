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
/-- The full spin plan for permutation 6 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate6 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (6 : Fin 83))
      (representativePermutationSpinPlan (6 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 7 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate7 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (7 : Fin 83))
      (representativePermutationSpinPlan (7 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 8 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate8 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (8 : Fin 83))
      (representativePermutationSpinPlan (8 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 9 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate9 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (9 : Fin 83))
      (representativePermutationSpinPlan (9 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 10 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate10 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (10 : Fin 83))
      (representativePermutationSpinPlan (10 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 11 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate11 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (11 : Fin 83))
      (representativePermutationSpinPlan (11 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
