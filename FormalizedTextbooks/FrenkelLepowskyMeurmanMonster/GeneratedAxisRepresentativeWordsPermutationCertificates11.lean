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
/-- The full spin plan for permutation 66 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate66 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (66 : Fin 83))
      (representativePermutationSpinPlan (66 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 67 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate67 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (67 : Fin 83))
      (representativePermutationSpinPlan (67 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 68 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate68 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (68 : Fin 83))
      (representativePermutationSpinPlan (68 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 69 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate69 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (69 : Fin 83))
      (representativePermutationSpinPlan (69 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 70 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate70 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (70 : Fin 83))
      (representativePermutationSpinPlan (70 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 71 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate71 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (71 : Fin 83))
      (representativePermutationSpinPlan (71 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
