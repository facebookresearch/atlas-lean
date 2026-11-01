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
/-- The full spin plan for permutation 78 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate78 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (78 : Fin 83))
      (representativePermutationSpinPlan (78 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 79 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate79 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (79 : Fin 83))
      (representativePermutationSpinPlan (79 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 80 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate80 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (80 : Fin 83))
      (representativePermutationSpinPlan (80 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 81 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate81 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (81 : Fin 83))
      (representativePermutationSpinPlan (81 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 82 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate82 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (82 : Fin 83))
      (representativePermutationSpinPlan (82 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
