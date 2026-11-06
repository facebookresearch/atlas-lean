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
/-- The full spin plan for permutation 54 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate54 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (54 : Fin 83))
      (representativePermutationSpinPlan (54 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 55 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate55 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (55 : Fin 83))
      (representativePermutationSpinPlan (55 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 56 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate56 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (56 : Fin 83))
      (representativePermutationSpinPlan (56 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 57 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate57 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (57 : Fin 83))
      (representativePermutationSpinPlan (57 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 58 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate58 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (58 : Fin 83))
      (representativePermutationSpinPlan (58 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 59 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate59 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (59 : Fin 83))
      (representativePermutationSpinPlan (59 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
