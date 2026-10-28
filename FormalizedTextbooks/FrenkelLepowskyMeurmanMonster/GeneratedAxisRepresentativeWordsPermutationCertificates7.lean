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
/-- The full spin plan for permutation 42 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate42 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (42 : Fin 83))
      (representativePermutationSpinPlan (42 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 43 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate43 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (43 : Fin 83))
      (representativePermutationSpinPlan (43 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 44 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate44 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (44 : Fin 83))
      (representativePermutationSpinPlan (44 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 45 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate45 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (45 : Fin 83))
      (representativePermutationSpinPlan (45 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 46 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate46 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (46 : Fin 83))
      (representativePermutationSpinPlan (46 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 47 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate47 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (47 : Fin 83))
      (representativePermutationSpinPlan (47 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
