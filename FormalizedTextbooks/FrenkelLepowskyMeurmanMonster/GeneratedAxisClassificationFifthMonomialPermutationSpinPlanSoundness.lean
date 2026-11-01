/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanProducts

/-! Soundness of the explicit matrix plans for the actual six fifth monomial words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exact finite plan validity certifies the full original spin operator, including all signs. -/
theorem generatedFifth_monomial_permutation_spin_plan_sound (k : Fin 6)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan k)) :
    representativeSpinCertificate (generatedFifthMonomialSpatialFiber k).val.1
      (generatedFifthMonomialPermutationSpinModel k).coordinate
      (generatedFifthMonomialPermutationSpinModel k).phase := by
  have hs : ∀ step ∈ generatedFifthMonomialPermutationSpinPlan k,
      representativeSpinCertificate (generatedFourthMonomialSpinLetter step.1)
        (generatedFourthMonomialLetterModel step.1).coordinate
        (generatedFourthMonomialLetterModel step.1).phase := by
    intro step _
    exact generatedFourth_monomial_letter_model step.1
  have h := representativeSpinPlan_certificate generatedFourthMonomialSpinLetter
    generatedFourthMonomialLetterModel (generatedFifthMonomialPermutationSpinPlan k) 1
    representativeSpinIdentityModel representativeSpinCertificate_one hs hc
  rw [representativeSpinPlanEvaluate_eq_product, one_mul,
    generatedFifth_monomial_permutation_plan_letters] at h
  have he : ((generatedFifthMonomialPermutationWord k).map
      generatedFourthMonomialFiberLetter).prod.val.1 =
      ((generatedFifthMonomialPermutationWord k).map generatedFourthMonomialSpinLetter).prod := by
    simpa only [generatedFourthMonomialSpinProjection, MonoidHom.coe_mk, OneHom.coe_mk] using
      generatedFifth_monomial_spin_word_projection (generatedFifthMonomialPermutationWord k)
  rw [← generatedFifth_monomial_permutation_word_fiber, he]
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
