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
/-- The full spin plan for permutation 0 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate0 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (0 : Fin 83))
      (representativePermutationSpinPlan (0 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 1 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate1 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (1 : Fin 83))
      (representativePermutationSpinPlan (1 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 2 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate2 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (2 : Fin 83))
      (representativePermutationSpinPlan (2 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 3 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate3 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (3 : Fin 83))
      (representativePermutationSpinPlan (3 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 4 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate4 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (4 : Fin 83))
      (representativePermutationSpinPlan (4 : Fin 83)) := by
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full spin plan for permutation 5 is kernel checked. -/
theorem representativePermutationSpin_plan_certificate5 :
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel (5 : Fin 83))
      (representativePermutationSpinPlan (5 : Fin 83)) := by
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
