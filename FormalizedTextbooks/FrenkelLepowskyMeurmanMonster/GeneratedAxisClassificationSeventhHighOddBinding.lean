/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpinPauliState
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhHighOddPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary

/-! Full preferred-Q phase of the unique high odd row in column sixteen. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original high plus pair has coordinates zero and twelve. -/
def generatedSeventhHighSourcePair : Fin 276 := griessPairIndex 0 12 (by decide)

/-- The original pair address has its literal physical coordinates. -/
theorem generatedSeventh_high_source_coordinates :
    griessCoordinatePair generatedSeventhHighSourcePair = (0, 12) := by
  simp [generatedSeventhHighSourcePair, griessPairIndex_coordinates]

/-- All eight stages of the preferred high-pair lift, including central signs. -/
def generatedSeventhHighQCache : Fin 8 → Q :=
  ![generatedAxisFourthQFromSpin (golayLabelCoefficients 2048) (golayLabelCoefficients 1037) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2050) (golayLabelCoefficients 13) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2830) (golayLabelCoefficients 0) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2830) (golayLabelCoefficients 0) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 6) (golayLabelCoefficients 1030) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2054) (golayLabelCoefficients 1024) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 4088) (golayLabelCoefficients 1275) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3060) (golayLabelCoefficients 2300) 0]

/-- Every cached step is the original generator's full extraspecial action. -/
theorem generatedSeventh_high_cache_steps :
    generatedSeventhHighQCache 1 =
      generatedSeventhQGenerator 2 (generatedSeventhHighQCache 0) ∧
    generatedSeventhHighQCache 2 =
      generatedSeventhQGenerator 0 (generatedSeventhHighQCache 1) ∧
    generatedSeventhHighQCache 3 =
      generatedSeventhQGenerator 1 (generatedSeventhHighQCache 2) ∧
    generatedSeventhHighQCache 4 =
      generatedSeventhQGenerator 0 (generatedSeventhHighQCache 3) ∧
    generatedSeventhHighQCache 5 =
      generatedSeventhQGenerator 2 (generatedSeventhHighQCache 4) ∧
    generatedSeventhHighQCache 6 =
      generatedSeventhQGenerator 1 (generatedSeventhHighQCache 5) ∧
    generatedSeventhHighQCache 7 =
      generatedSeventhQGenerator 2 (generatedSeventhHighQCache 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

private theorem high_initial : generatedSeventhHighQCache 0 =
    griessShortQ (Sum.inl (1, generatedSeventhHighSourcePair)) := by
  change generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
    (golayLabelCoefficients 1037) 0 = _
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedAxisFourthQFromSpin_translation, griessPairQ_translation]
    ext i
    fin_cases i <;> decide +kernel
  · rw [generatedAxisFourthQFromSpin_modulation, griessPairQ_modulation]
    ext i
    change _ = (golayGeneratorBit i (griessCoordinatePair generatedSeventhHighSourcePair).1 :
      ZMod 2) + (golayGeneratorBit i (griessCoordinatePair generatedSeventhHighSourcePair).2 :
      ZMod 2)
    rw [generatedSeventh_high_source_coordinates]
    fin_cases i <;> decide +kernel
  · rw [generatedAxisFourthQFromSpin_coeff, griessShortQ_coeff]

private theorem high_final : generatedSeventhHighQCache 7 =
    griessShortQ (Sum.inr (Sum.inr (1012, 16))) := by
  change generatedAxisFourthQFromSpin (golayLabelCoefficients 3060)
    (golayLabelCoefficients 2300) 0 = _
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedAxisFourthQFromSpin_translation, griessOdd_translation]
    ext i
    fin_cases i <;> decide +kernel
  · rw [generatedAxisFourthQFromSpin_modulation, griessOdd_modulation]
    ext i
    fin_cases i <;> decide +kernel
  · rw [generatedAxisFourthQFromSpin_coeff, griessShortQ_coeff]

/-- The unique high source row has preferred-Q image with central coefficient zero. -/
theorem generatedSeventh_high_odd_preferred_transport :
    spinConjugation generatedSeventhLocalFiber.val.1
      (griessShortQ (Sum.inl (1, generatedSeventhHighSourcePair))) =
        griessShortQ (Sum.inr (Sum.inr (1012, 16))) := by
  rw [← high_initial, generatedSeventh_spin_conjugation]
  rcases generatedSeventh_high_cache_steps with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  unfold generatedSeventhQImage generatedSeventhQWord
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, high_final]

/-- The actual signed short permutation reaches the specified odd label. -/
theorem generatedSeventh_high_odd_permutation :
    griessShortPermutation generatedSeventhLocalFiber.val.2
      (Sum.inl (1, generatedSeventhHighSourcePair)) =
        Sum.inr (Sum.inr (1012, 16)) := by
  have hb := griessShortQ_image_base generatedSeventhLocalFiber
    (Sum.inl (1, generatedSeventhHighSourcePair))
  rw [generatedSeventh_high_odd_preferred_transport] at hb
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact (congrArg Multiplicative.toAdd hb).symm

/-- The actual incoming coefficient is positive three quarters. -/
theorem generatedSeventh_high_odd_coefficient :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (1012, 16))) = (3 / 4 : ℝ) := by
  rw [generatedFourth_local_short, ← generatedSeventh_high_odd_permutation,
    localShortOperator_image]
  have hp : localShortPhase generatedSeventhLocalFiber
      (Sum.inl (1, generatedSeventhHighSourcePair)) = 0 := by
    unfold localShortPhase
    rw [generatedSeventh_high_odd_preferred_transport, griessShortQ_coeff]
  rw [hp, qSign_zero, one_mul, generatedSeventh_original_pair_coordinate,
    generatedSeventh_high_source_coordinates]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
