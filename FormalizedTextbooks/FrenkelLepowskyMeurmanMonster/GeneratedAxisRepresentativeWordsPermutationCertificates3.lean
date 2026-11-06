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
/-- The full spin plan for permutation 18 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate18 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (18 : Fin 83))
      (representativePermutationSpinPlan (18 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 19 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate19 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (19 : Fin 83))
      (representativePermutationSpinPlan (19 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 20 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate20 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (20 : Fin 83))
      (representativePermutationSpinPlan (20 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 21 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate21 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (21 : Fin 83))
      (representativePermutationSpinPlan (21 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 22 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate22 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (22 : Fin 83))
      (representativePermutationSpinPlan (22 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 23 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate23 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (23 : Fin 83))
      (representativePermutationSpinPlan (23 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
