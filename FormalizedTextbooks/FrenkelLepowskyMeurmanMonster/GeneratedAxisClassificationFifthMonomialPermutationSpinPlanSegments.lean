/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanDecidable

/-! Bounded checks concatenate to certify the complete original signed phase plan. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Adjacent verified phase plans concatenate without changing the original group product. -/
theorem generatedFifth_monomial_plan_valid_append {ι : Type} (models : ι → RepresentativeSpinModel)
    (a : RepresentativeSpinModel) (p q : RepresentativeSpinPlan ι)
    (hp : representativeSpinPlanValid models a p)
    (hq : representativeSpinPlanValid models (representativeSpinPlanEnd a p) q) :
    representativeSpinPlanValid models a (p ++ q) := by
  induction p generalizing a with
  | nil => exact hq
  | cons s p ih =>
    rcases s with ⟨l, b⟩
    exact ⟨hp.1, ih b hp.2 hq⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
