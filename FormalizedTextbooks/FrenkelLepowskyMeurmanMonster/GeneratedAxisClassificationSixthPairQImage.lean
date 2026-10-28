/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairQImageData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts

/-! A complete original preferred-Q image formula for every genuine source pair address. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact image of a pair lift, assembled from the verified original basis images. -/
def generatedSixthPairQImage (s : Fin 2) (m : SpinIndex) : Q :=
  generatedSixthAffinePauliProduct generatedSixthPairQBasisImages m *
    (if s = 0 then 1 else generatedSixthPairQOmegaImage)

/-- The all-one source-code coefficient vector is the frame translation basis vector. -/
theorem generatedSixth_pair_Q_omega_label :
    golayLabelCoefficients 2048 = Pi.single (11 : Fin 12) 1 := by
  funext i
  fin_cases i <;> decide +kernel

/-- The source pair lift is exactly its genuine modulation and frame-translation data. -/
theorem generatedSixth_pair_Q_source (s : Fin 2) (p : Fin 276) :
    generatedAxisFourthQFromSpin (if s = 0 then 0 else golayLabelCoefficients 2048)
      (griessPairSyndrome p) 0 = griessShortQ (Sum.inl (s,p)) := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedAxisFourthQFromSpin_translation, griessPairQ_translation,
      generatedSixth_pair_Q_omega_label]
  · rw [generatedAxisFourthQFromSpin_modulation, griessPairQ_modulation]
  · rw [generatedAxisFourthQFromSpin_coeff, griessShortQ_coeff]

private theorem zero_lift : generatedAxisFourthQFromSpin 0 0 0 = 1 := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedAxisFourthQFromSpin_translation]
    rfl
  · rw [generatedAxisFourthQFromSpin_modulation]
    rfl
  · rw [generatedAxisFourthQFromSpin_coeff]
    rfl

/-- The basis image formula equals the actual original full spin conjugation on all pair lifts. -/
theorem generatedSixth_pair_Q_image (s : Fin 2) (p : Fin 276) :
    spinConjugation generatedSixthLocalFiber.val.1 (griessShortQ (Sum.inl (s,p))) =
      generatedSixthPairQImage s (griessPairSyndrome p) := by
  rw [← generatedSixth_pair_Q_source]
  let φ : Q →* Q := (spinConjugation generatedSixthLocalFiber.val.1).toMonoidHom
  change φ _ = _
  rw [generatedSixth_pair_Q_image_product]
  simp_rw [show ∀ j, φ (generatedSixthPairModulationBasis j) =
    generatedSixthPairQBasisImages j from generatedSixth_pair_Q_basis_image]
  unfold generatedSixthPairQImage
  congr 1
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · simp only [ite_true]
    rw [zero_lift]
    exact map_one φ
  · simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false]
    exact generatedSixth_pair_Q_omega_image

/-- Every genuine middle short coefficient phase is given by the complete finite basis formula. -/
theorem generatedSixth_pair_Q_phase (s : Fin 2) (p : Fin 276) :
    generatedSixthMiddleShortPhase (s,p) =
      Multiplicative.toAdd (generatedSixthPairQImage s (griessPairSyndrome p)).coeff := by
  unfold generatedSixthMiddleShortPhase localShortPhase
  rw [generatedSixth_pair_Q_image]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
