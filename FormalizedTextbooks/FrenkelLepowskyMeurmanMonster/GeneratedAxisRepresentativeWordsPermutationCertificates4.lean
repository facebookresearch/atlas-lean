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
/-- The full spin plan for permutation 24 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate24 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (24 : Fin 83))
      (representativePermutationSpinPlan (24 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 25 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate25 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (25 : Fin 83))
      (representativePermutationSpinPlan (25 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 26 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate26 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (26 : Fin 83))
      (representativePermutationSpinPlan (26 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 27 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate27 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (27 : Fin 83))
      (representativePermutationSpinPlan (27 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 28 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate28 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (28 : Fin 83))
      (representativePermutationSpinPlan (28 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 29 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate29 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (29 : Fin 83))
      (representativePermutationSpinPlan (29 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
