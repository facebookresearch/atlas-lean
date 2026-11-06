/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact multiplication bridges between finite certificate plans and actual fiber words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlan

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Plan evaluation is the ordinary actual group product in precisely the recorded order. -/
theorem representativeSpinPlanEvaluate_eq_product {ι : Type}
    (generators : ι → SpinHolomorph) (g : SpinHolomorph)
    (plan : RepresentativeSpinPlan ι) :
    representativeSpinPlanEvaluate generators g plan =
      g * ((plan.map Prod.fst).map generators).prod := by
  induction plan generalizing g with
  | nil => simp [representativeSpinPlanEvaluate]
  | cons step rest ih =>
    rcases step with ⟨letter, next⟩
    simp only [representativeSpinPlanEvaluate, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- Projection to spin is a genuine group homomorphism on the actual defining fiber. -/
def representativeFiberSpin : localFiberSubgroup →* SpinHolomorph where
  toFun g := g.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The spin of an actual fiber word is exactly the product of its actual spin components. -/
theorem representativeFiberSpin_list_prod (word : List localFiberSubgroup) :
    representativeFiberSpin word.prod = (word.map representativeFiberSpin).prod :=
  map_list_prod representativeFiberSpin word

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
