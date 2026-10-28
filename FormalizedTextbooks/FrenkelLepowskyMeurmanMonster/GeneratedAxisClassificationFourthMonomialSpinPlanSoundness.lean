/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanProducts

/-! Soundness of the explicit matrix plans for the actual four monomial words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exact finite plan validity certifies the full original spin operator, including all signs. -/
theorem generatedFourth_monomial_spin_plan_sound (k : Fin 4)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFourthMonomialSpinPlan k)) :
    representativeSpinCertificate (generatedFourthMonomialFiber k).val.1
      (generatedFourthMonomialSpinModel k).coordinate
      (generatedFourthMonomialSpinModel k).phase := by
  have hs : ∀ step ∈ generatedFourthMonomialSpinPlan k,
      representativeSpinCertificate (generatedFourthMonomialSpinLetter step.1)
        (generatedFourthMonomialLetterModel step.1).coordinate
        (generatedFourthMonomialLetterModel step.1).phase := by
    intro step _
    exact generatedFourth_monomial_letter_model step.1
  have h := representativeSpinPlan_certificate generatedFourthMonomialSpinLetter
    generatedFourthMonomialLetterModel (generatedFourthMonomialSpinPlan k) 1
    representativeSpinIdentityModel representativeSpinCertificate_one hs hc
  rw [representativeSpinPlanEvaluate_eq_product, one_mul,
    generatedFourth_monomial_plan_letters] at h
  rw [generatedFourth_monomial_spin_projection]
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
