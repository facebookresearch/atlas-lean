/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Complete Q conjugation of the genuine corrected C-inverse/Xi/C word, including its center. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original inverse C image with its full signed quadratic cochain. -/
def generatedSixthCInverseImage (q : Q) : Q :=
  monsterMonomialDiagonalImage
    (fun i j => representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1) i j)
    (monsterMonomialPermutationImage generatedSixthCTranslation.symm q)

/-- The inverse image formula is conjugation by the entire original inverse spin word. -/
theorem generatedSixth_C_inverse_conjugation (q : Q) :
    spinConjugation leechRootedA2SixthXiTransportFiber.val.1⁻¹ q =
      generatedSixthCInverseImage q := by
  apply generatedSixth_spin_conjugation_of_monomial _ generatedSixthCTranslation.symm _ _ q
  exact generatedSixth_permutation_profile_inverse_spin 1

/-- Entire original C-inverse/Xi/C Q image, retaining both genuine Gaussian phases. -/
def generatedSixthXiRawQImage (q : Q) : Q :=
  generatedSixthCInverseImage (xiSpinGImage (xiSpinGammaImage (generatedSixthCImage q)))

/-- The full finite formula is the original raw Xi-word spin conjugation on every Q element. -/
theorem generatedSixth_xi_raw_QImage (q : Q) :
    spinConjugation (generatedSixthRawGenerator 4).val.1 q = generatedSixthXiRawQImage q := by
  change spinConjugation
    (leechRootedA2SixthXiTransportFiber.val.1⁻¹ * xiSpinHolomorph *
      leechRootedA2SixthXiTransportFiber.val.1) q = _
  rw [map_mul, map_mul]
  change spinConjugation leechRootedA2SixthXiTransportFiber.val.1⁻¹
    (spinConjugation xiSpinHolomorph
      (spinConjugation leechRootedA2SixthXiTransportFiber.val.1 q)) = _
  rw [generatedSixth_C_conjugation, xiSpinHolomorph_conjugation,
    generatedSixth_C_inverse_conjugation]
  rfl

/-- Full corrected original Q conjugation, retaining the actual inner-Q central correction. -/
def generatedSixthXiQImage (q : Q) : Q :=
  generatedSixthGeneratorCorrection 4 * generatedSixthXiRawQImage q *
    (generatedSixthGeneratorCorrection 4)⁻¹

/-- This full Q image equals the genuine corrected original spin conjugation everywhere. -/
theorem generatedSixth_xi_QImage (q : Q) :
    spinConjugation (generatedSixthCorrectedGenerator 4).val.1 q = generatedSixthXiQImage q := by
  change spinConjugation (spinHolomorphIncl (generatedSixthGeneratorCorrection 4) *
    (generatedSixthRawGenerator 4).val.1) q = _
  rw [map_mul]
  change spinConjugation (spinHolomorphIncl (generatedSixthGeneratorCorrection 4))
    (spinConjugation (generatedSixthRawGenerator 4).val.1 q) = _
  rw [spinConjugation_incl, generatedSixth_xi_raw_QImage]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
