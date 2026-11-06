/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactors

/-! The integer spin action of each root-two monomial word from its valid plan. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every valid intermediate phase plan certifies the whole root-two spin word. -/
theorem generatedFeasibleAmbientTenth_monomial_plan_sound (k : Fin 5)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFeasibleAmbientTenthMonomialPlan k)) :
    representativeSpinCertificate
      ((generatedFeasibleAmbientTenthMonomialWord k).map generatedFourthMonomialSpinLetter).prod
      (generatedFeasibleAmbientTenthMonomialModel k).coordinate
      (generatedFeasibleAmbientTenthMonomialModel k).phase := by
  have hs : ∀ step ∈ generatedFeasibleAmbientTenthMonomialPlan k,
      representativeSpinCertificate (generatedFourthMonomialSpinLetter step.1)
        (generatedFourthMonomialLetterModel step.1).coordinate
        (generatedFourthMonomialLetterModel step.1).phase := by
    intro step _
    exact generatedFourth_monomial_letter_model step.1
  have h := representativeSpinPlan_certificate generatedFourthMonomialSpinLetter
    generatedFourthMonomialLetterModel (generatedFeasibleAmbientTenthMonomialPlan k) 1
    representativeSpinIdentityModel representativeSpinCertificate_one hs hc
  rw [representativeSpinPlanEvaluate_eq_product, one_mul] at h
  exact h

/-- Compact integer pullback, retaining the full quadratic phase. -/
def generatedFeasibleAmbientTenthMonomialSpinCompact (k : Fin 5) (u : Fin 4096 → ℤ) (a : Fin 4096)
    : ℤ :=
  generatedAxisGlobalIntSign
    (monsterMonomialQuadratic (fun i j => (generatedFeasibleAmbientTenthMonomialModel k).phase i j)
      (golayLabelCoefficients a)) *
    u (generatedAxisGlobalSpinLabel
      ((generatedFeasibleAmbientTenthMonomialModel k).coordinate *ᵥ golayLabelCoefficients a))

/-- Every root-two integer spin coordinate equals the compact model formula. -/
theorem generatedFeasibleAmbientTenth_monomial_spin_compact (k : Fin 5)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFeasibleAmbientTenthMonomialPlan k))
    (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddMonomialSpinInteger (generatedFeasibleAmbientTenthMonomialWord k) u =
      generatedFeasibleAmbientTenthMonomialSpinCompact k u := by
  funext a
  apply Int.cast_injective (α := ℝ)
  have hs := generatedFeasibleAmbientTenth_monomial_plan_sound k hc
    (fun t => (u (generatedAxisGlobalSpinLabel t) : ℝ)) (golayLabelCoefficients a)
  have hw := generatedFourth_monomial_spin_word_apply
    (generatedFeasibleAmbientTenthMonomialWord k)
    (fun t => (u (generatedAxisGlobalSpinLabel t) : ℝ)) (golayLabelCoefficients a)
  simp only [generatedAxisGlobalOddMonomialSpinInteger,
    generatedFeasibleAmbientTenthMonomialSpinCompact, Int.cast_mul,
    generatedAxisGlobalIntSign_real]
  exact hw.symm.trans hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
