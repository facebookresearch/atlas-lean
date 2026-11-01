/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialPlanCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialPlanCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialCacheCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialCacheCheck01

/-! Complete actual source-operator consequences of the bounded original certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Both entire original source plans have all their genuine phase edges certified. -/
theorem generatedTwelfth_tensor_source_monomial_plans_valid (k : Fin 2) :
    representativeSpinPlanValid generatedFourthMonomialLetterModel representativeSpinIdentityModel
      (generatedTwelfthTensorSourceMonomialPlan k) := by
  fin_cases k
  · exact generatedTwelfth_tensor_source_monomial_plan_check00
  · exact generatedTwelfth_tensor_source_monomial_plan_check01

/-- Every actual original source spin coordinate has its complete cached signed pullback. -/
theorem generatedTwelfth_tensor_source_monomial_cached_actual (k : Fin 2)
    (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddMonomialSpinInteger (generatedTwelfthTensorSourceMonomialWord k) u =
      fun a => generatedTwelfthTensorSourceMonomialPhaseSign k a *
        u (generatedTwelfthTensorSourceMonomialPull k a) := by
  rw [generatedTwelfth_tensor_source_monomial_spin_compact k
    (generatedTwelfth_tensor_source_monomial_plans_valid k)]
  funext a
  have h : generatedAxisGlobalSpinLabel
        ((generatedTwelfthTensorSourceMonomialModel k).coordinate *ᵥ golayLabelCoefficients a) =
      generatedTwelfthTensorSourceMonomialPull k a ∧
    generatedAxisGlobalIntSign
        (monsterMonomialQuadratic
          (fun i j => (generatedTwelfthTensorSourceMonomialModel k).phase i j)
          (golayLabelCoefficients a)) = generatedTwelfthTensorSourceMonomialPhaseSign k a := by
    fin_cases k
    · exact generatedTwelfth_tensor_source_monomial_cache_check00 a
    · exact generatedTwelfth_tensor_source_monomial_cache_check01 a
  simp only [generatedTwelfthTensorSourceMonomialSpinCompact, h.1, h.2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
