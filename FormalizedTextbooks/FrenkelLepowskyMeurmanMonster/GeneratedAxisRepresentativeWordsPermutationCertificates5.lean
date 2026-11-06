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
/-- The full spin plan for permutation 30 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate30 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (30 : Fin 83))
      (representativePermutationSpinPlan (30 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 31 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate31 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (31 : Fin 83))
      (representativePermutationSpinPlan (31 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 32 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate32 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (32 : Fin 83))
      (representativePermutationSpinPlan (32 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 33 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate33 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (33 : Fin 83))
      (representativePermutationSpinPlan (33 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 34 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate34 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (34 : Fin 83))
      (representativePermutationSpinPlan (34 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 35 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate35 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (35 : Fin 83))
      (representativePermutationSpinPlan (35 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
