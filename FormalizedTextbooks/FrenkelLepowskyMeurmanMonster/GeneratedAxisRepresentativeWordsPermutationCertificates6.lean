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
/-- The full spin plan for permutation 36 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate36 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (36 : Fin 83))
      (representativePermutationSpinPlan (36 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 37 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate37 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (37 : Fin 83))
      (representativePermutationSpinPlan (37 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 38 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate38 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (38 : Fin 83))
      (representativePermutationSpinPlan (38 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 39 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate39 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (39 : Fin 83))
      (representativePermutationSpinPlan (39 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 40 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate40 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (40 : Fin 83))
      (representativePermutationSpinPlan (40 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 41 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate41 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (41 : Fin 83))
      (representativePermutationSpinPlan (41 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
