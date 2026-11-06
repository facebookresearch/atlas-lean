/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialPlanCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialPlanCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialPlanCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialPlanCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialPlanCheck04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialCacheCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialCacheCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialCacheCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialCacheCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialCacheCheck04

/-! Root-two monomial words act by their cached signed pullbacks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All five root-two plans have their phase edges certified. -/
theorem generatedFeasibleAmbientTenth_monomial_plans_valid (k : Fin 5) :
    representativeSpinPlanValid generatedFourthMonomialLetterModel representativeSpinIdentityModel
      (generatedFeasibleAmbientTenthMonomialPlan k) := by
  fin_cases k
  · exact generatedFeasibleAmbientTenth_monomial_plan_check00
  · exact generatedFeasibleAmbientTenth_monomial_plan_check01
  · exact generatedFeasibleAmbientTenth_monomial_plan_check02
  · exact generatedFeasibleAmbientTenth_monomial_plan_check03
  · exact generatedFeasibleAmbientTenth_monomial_plan_check04

/-- Every root-two monomial spin coordinate has its cached signed pullback. -/
theorem generatedFeasibleAmbientTenth_monomial_cached_actual (k : Fin 5) (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddMonomialSpinInteger (generatedFeasibleAmbientTenthMonomialWord k) u =
      fun a => generatedFeasibleAmbientTenthMonomialPhaseSign k a * u
          (generatedFeasibleAmbientTenthMonomialPull k a) := by
  rw [generatedFeasibleAmbientTenth_monomial_spin_compact k
      (generatedFeasibleAmbientTenth_monomial_plans_valid k)]
  funext a
  have h : generatedAxisGlobalSpinLabel
        ((generatedFeasibleAmbientTenthMonomialModel k).coordinate *ᵥ golayLabelCoefficients a) =
      generatedFeasibleAmbientTenthMonomialPull k a ∧
    generatedAxisGlobalIntSign
        (monsterMonomialQuadratic
          (fun i j => (generatedFeasibleAmbientTenthMonomialModel k).phase i j)
          (golayLabelCoefficients a)) = generatedFeasibleAmbientTenthMonomialPhaseSign k a := by
    fin_cases k
    · exact generatedFeasibleAmbientTenth_monomial_cache_check00 a
    · exact generatedFeasibleAmbientTenth_monomial_cache_check01 a
    · exact generatedFeasibleAmbientTenth_monomial_cache_check02 a
    · exact generatedFeasibleAmbientTenth_monomial_cache_check03 a
    · exact generatedFeasibleAmbientTenth_monomial_cache_check04 a
  simp only [generatedFeasibleAmbientTenthMonomialSpinCompact, h.1, h.2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
