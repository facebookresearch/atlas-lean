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
/-- The full spin plan for permutation 48 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate48 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (48 : Fin 83))
      (representativePermutationSpinPlan (48 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 49 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate49 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (49 : Fin 83))
      (representativePermutationSpinPlan (49 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 50 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate50 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (50 : Fin 83))
      (representativePermutationSpinPlan (50 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 51 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate51 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (51 : Fin 83))
      (representativePermutationSpinPlan (51 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 52 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate52 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (52 : Fin 83))
      (representativePermutationSpinPlan (52 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 53 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate53 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (53 : Fin 83))
      (representativePermutationSpinPlan (53 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
