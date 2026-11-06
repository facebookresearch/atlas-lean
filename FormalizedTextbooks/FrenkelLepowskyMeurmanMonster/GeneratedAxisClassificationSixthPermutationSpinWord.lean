/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsTargetSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationTransport

/-! Full signed monomial spin formulas for arbitrary original source permutation words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The source-letter model uses the same full signed compact-node certificates. -/
def generatedSixthPermutationSpinLetterModel (t : Fin 4) : RepresentativeSpinModel :=
  if h : t.val < 2 then representativeNodeSpinModel (⟨t.val, by omega⟩, true)
  else representativeNodeSpinModel (⟨t.val - 2, by omega⟩, false)

/-- Each original source permutation letter retains the certified full quadratic spin sign. -/
theorem generatedSixth_permutation_spin_letter (t : Fin 4) :
    representativeSpinCertificate (leechRootedA2GeneratingLetterFiber t).val.1
      (generatedSixthPermutationSpinLetterModel t).coordinate
      (generatedSixthPermutationSpinLetterModel t).phase := by
  fin_cases t
  · change representativeSpinCertificate (monsterSourcePermutationSpin 0)
      (representativeNodeSpinModel (0, true)).coordinate
      (representativeNodeSpinModel (0, true)).phase
    have h := representativeNodeSpin_signed_certificate (0, true)
    change representativeSpinCertificate ((monsterSourcePermutationSpin 0)⁻¹)⁻¹ _ _ at h
    simpa only [inv_inv] using h
  · change representativeSpinCertificate (monsterSourcePermutationSpin 1)
      (representativeNodeSpinModel (1, true)).coordinate
      (representativeNodeSpinModel (1, true)).phase
    have h := representativeNodeSpin_signed_certificate (1, true)
    change representativeSpinCertificate ((monsterSourcePermutationSpin 1)⁻¹)⁻¹ _ _ at h
    simpa only [inv_inv] using h
  · exact representativeNodeSpin_signed_certificate (0, false)
  · exact representativeNodeSpin_signed_certificate (1, false)

/-- The signed pullback model of a source word, using the genuine matrix composition rule. -/
def generatedSixthPermutationSpinWordModel : List (Fin 4) → RepresentativeSpinModel
  | [] => ⟨1, 0⟩
  | t :: w =>
    let a := generatedSixthPermutationSpinLetterModel t
    let b := generatedSixthPermutationSpinWordModel w
    ⟨b.coordinate * a.coordinate,
      a.phase + a.coordinateᵀ * b.phase * a.coordinate⟩

/-- Every original full permutation word has its exact signed spin operator formula. -/
theorem generatedSixth_permutation_spin_word (w : List (Fin 4)) :
    representativeSpinCertificate (leechRootedA2GeneratingWordFiber w).val.1
      (generatedSixthPermutationSpinWordModel w).coordinate
      (generatedSixthPermutationSpinWordModel w).phase := by
  induction w with
  | nil => exact representativeSpinCertificate_one
  | cons t w ih =>
    change representativeSpinCertificate
      ((leechRootedA2GeneratingLetterFiber t).val.1 *
        (leechRootedA2GeneratingWordFiber w).val.1)
      ((generatedSixthPermutationSpinWordModel w).coordinate *
        (generatedSixthPermutationSpinLetterModel t).coordinate)
      ((generatedSixthPermutationSpinLetterModel t).phase +
        (generatedSixthPermutationSpinLetterModel t).coordinateᵀ *
          (generatedSixthPermutationSpinWordModel w).phase *
            (generatedSixthPermutationSpinLetterModel t).coordinate)
    exact representativeSpinCertificate_mul _ _ _ _ _ _
      (generatedSixth_permutation_spin_letter t) ih

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
