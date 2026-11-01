/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactors

/-! Genuine complete integer spin action from the bounded original source plans. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every valid intermediate phase plan certifies the whole original spin word. -/
theorem generatedTwelfth_tensor_source_monomial_plan_sound (k : Fin 2)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedTwelfthTensorSourceMonomialPlan k)) :
    representativeSpinCertificate
      ((generatedTwelfthTensorSourceMonomialWord k).map generatedFourthMonomialSpinLetter).prod
      (generatedTwelfthTensorSourceMonomialModel k).coordinate
      (generatedTwelfthTensorSourceMonomialModel k).phase := by
  have hs : ∀ step ∈ generatedTwelfthTensorSourceMonomialPlan k,
      representativeSpinCertificate (generatedFourthMonomialSpinLetter step.1)
        (generatedFourthMonomialLetterModel step.1).coordinate
        (generatedFourthMonomialLetterModel step.1).phase := by
    intro step _
    exact generatedFourth_monomial_letter_model step.1
  have h := representativeSpinPlan_certificate generatedFourthMonomialSpinLetter
    generatedFourthMonomialLetterModel (generatedTwelfthTensorSourceMonomialPlan k) 1
    representativeSpinIdentityModel representativeSpinCertificate_one hs hc
  rw [representativeSpinPlanEvaluate_eq_product, one_mul] at h
  exact h

/-- Complete compact integer pullback, retaining the full genuine quadratic phase. -/
def generatedTwelfthTensorSourceMonomialSpinCompact (k : Fin 2)
    (u : Fin 4096 → ℤ) (a : Fin 4096) : ℤ :=
  generatedAxisGlobalIntSign
    (monsterMonomialQuadratic (fun i j => (generatedTwelfthTensorSourceMonomialModel k).phase i j)
      (golayLabelCoefficients a)) *
    u (generatedAxisGlobalSpinLabel
      ((generatedTwelfthTensorSourceMonomialModel k).coordinate *ᵥ golayLabelCoefficients a))

/-- Every original integer spin coordinate equals the genuine compact model formula. -/
theorem generatedTwelfth_tensor_source_monomial_spin_compact (k : Fin 2)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedTwelfthTensorSourceMonomialPlan k))
    (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddMonomialSpinInteger (generatedTwelfthTensorSourceMonomialWord k) u =
      generatedTwelfthTensorSourceMonomialSpinCompact k u := by
  funext a
  apply Int.cast_injective (α := ℝ)
  have hs := generatedTwelfth_tensor_source_monomial_plan_sound k hc
    (fun t => (u (generatedAxisGlobalSpinLabel t) : ℝ)) (golayLabelCoefficients a)
  have hw := generatedFourth_monomial_spin_word_apply
    (generatedTwelfthTensorSourceMonomialWord k)
    (fun t => (u (generatedAxisGlobalSpinLabel t) : ℝ)) (golayLabelCoefficients a)
  simp only [generatedAxisGlobalOddMonomialSpinInteger,
    generatedTwelfthTensorSourceMonomialSpinCompact, Int.cast_mul,
    generatedAxisGlobalIntSign_real]
  exact hw.symm.trans hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
