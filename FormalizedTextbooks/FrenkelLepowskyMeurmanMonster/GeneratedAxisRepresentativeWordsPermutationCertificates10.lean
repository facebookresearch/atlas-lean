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
/-- The full spin plan for permutation 60 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate60 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (60 : Fin 83))
      (representativePermutationSpinPlan (60 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 61 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate61 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (61 : Fin 83))
      (representativePermutationSpinPlan (61 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 62 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate62 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (62 : Fin 83))
      (representativePermutationSpinPlan (62 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 63 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate63 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (63 : Fin 83))
      (representativePermutationSpinPlan (63 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 64 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate64 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (64 : Fin 83))
      (representativePermutationSpinPlan (64 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 65 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate65 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (65 : Fin 83))
      (representativePermutationSpinPlan (65 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
