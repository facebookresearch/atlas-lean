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
/-- The full spin plan for permutation 72 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate72 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (72 : Fin 83))
      (representativePermutationSpinPlan (72 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 73 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate73 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (73 : Fin 83))
      (representativePermutationSpinPlan (73 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 74 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate74 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (74 : Fin 83))
      (representativePermutationSpinPlan (74 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 75 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate75 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (75 : Fin 83))
      (representativePermutationSpinPlan (75 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 76 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate76 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (76 : Fin 83))
      (representativePermutationSpinPlan (76 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 77 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate77 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (77 : Fin 83))
      (representativePermutationSpinPlan (77 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
