/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords

/-! Actual physical and signed-short certificates for the four original monomial words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Literal coordinate images of the four genuine permutation words. -/
def generatedFourthMonomialImages : Fin 4 → Fin 24 → Fin 24 :=
  ![![21, 14, 17, 3, 6, 5, 4, 10, 8, 9, 7, 11, 12, 22, 1, 16, 15, 2, 18, 23, 20, 0, 13, 19],
    ![3, 1, 2, 0, 4, 6, 5, 7, 11, 9, 10, 8, 12, 14, 13, 15, 22, 20, 23, 21, 17, 19, 16, 18],
    ![0, 12, 22, 19, 4, 9, 7, 6, 8, 5, 10, 11, 1, 13, 20, 16, 15, 17, 23, 3, 14, 21, 2, 18],
    ![1, 0, 3, 2, 4, 5, 6, 7, 11, 10, 9, 8, 14, 15, 12, 13, 16, 17, 18, 19, 21, 20, 23, 22]]

/-- Every literal image is the actual product of the two verified source permutations. -/
theorem generatedFourth_monomial_images : ∀ k : Fin 4, ∀ i : Fin 24,
    (generatedFourthMonomialPermutation k).val i = generatedFourthMonomialImages k i := by
  decide +kernel

/-- The actual words preserve the genuine code-fourteen octad. -/
theorem generatedFourth_monomial_code_certificate : ∀ k : Fin 4, ∀ i : Fin 24,
    golayEncoder (golayLabelCoefficients 14) ((generatedFourthMonomialPermutation k).val.symm i) =
      golayEncoder (golayLabelCoefficients 14) i := by
  decide +kernel

/-- The original preferred pair is fixed or negated with its genuine signed coordinates. -/
theorem generatedFourth_monomial_pair_certificate : ∀ k : Fin 4, ∀ i : Fin 24,
    generatedFourthFlagPairIntegral ((generatedFourthMonomialPermutation k).val.symm i) =
      if k.val % 2 = 0 then generatedFourthFlagPairIntegral i
      else -generatedFourthFlagPairIntegral i := by
  decide +kernel

/-- The actual coordinate word of the distinguished flag octad is preserved. -/
theorem generatedFourth_monomial_octad_word (k : Fin 4) :
    golayPermute (generatedFourthMonomialPermutation k).val
      (golayOctadWord generatedFourthFlagOctad) = golayOctadWord generatedFourthFlagOctad := by
  have hc : golayOctadWord generatedFourthFlagOctad =
      golayEncoder (golayLabelCoefficients 14) := by
    unfold golayOctadWord
    rw [generatedFourthFlagOctad_label]
  rw [hc]
  funext i
  exact generatedFourth_monomial_code_certificate k i

/-- Every actual four-word lift preserves the full integral E8 section in both directions. -/
theorem generatedFourth_monomial_section_preserves (k : Fin 4) :
    generatedOctadPreserves (golayOctadWord generatedFourthFlagOctad)
      (generatedFourthMonomialFiber k).val.2 := by
  rw [generatedFourth_monomial_spatial]
  intro u
  exact generatedOctadSupported_permutation _ _ _ (generatedFourth_monomial_octad_word k) u

/-- The actual four-word spatial lifts preserve the preferred physical short vector up to sign. -/
theorem generatedFourth_monomial_short_vector (k : Fin 4) :
    (generatedFourthMonomialFiber k).val.2.val (griessShortVector generatedFourthFlagShort) =
      griessShortVector generatedFourthFlagShort ∨
    (generatedFourthMonomialFiber k).val.2.val (griessShortVector generatedFourthFlagShort) =
      -griessShortVector generatedFourthFlagShort := by
  rw [generatedFourth_monomial_spatial]
  by_cases hk : k.val % 2 = 0
  · left
    funext i
    change ((griessShortIntegral generatedFourthFlagShort
      ((generatedFourthMonomialPermutation k).val.symm i) : ℝ) / Real.sqrt 8) =
        (griessShortIntegral generatedFourthFlagShort i : ℝ) / Real.sqrt 8
    rw [generatedFourth_flag_pair_integral]
    have h := generatedFourth_monomial_pair_certificate k i
    rw [ite_eq_left hk] at h
    exact congrArg (fun z : ℤ => (z : ℝ) / Real.sqrt 8) h
  · right
    funext i
    change ((griessShortIntegral generatedFourthFlagShort
      ((generatedFourthMonomialPermutation k).val.symm i) : ℝ) / Real.sqrt 8) =
        -((griessShortIntegral generatedFourthFlagShort i : ℝ) / Real.sqrt 8)
    rw [generatedFourth_flag_pair_integral]
    have h := generatedFourth_monomial_pair_certificate k i
    rw [ite_eq_right hk] at h
    simpa only [Int.cast_neg, neg_div] using
      congrArg (fun z : ℤ => (z : ℝ) / Real.sqrt 8) h

/-- Each genuine original permutation word fixes the actual short-line label. -/
theorem generatedFourth_monomial_short_label (k : Fin 4) :
    griessShortPermutation (generatedFourthMonomialFiber k).val.2 generatedFourthFlagShort =
      generatedFourthFlagShort := by
  apply centralizer_shortVector_sign_unique
  rcases generatedFourth_monomial_short_vector k with hp | hn
  · rcases griessShortPermutation_vector (generatedFourthMonomialFiber k).val.2
        generatedFourthFlagShort with h | h
    · exact Or.inl (h.symm.trans hp)
    · have he := h.symm.trans hp
      exact Or.inr (by simpa only [neg_neg] using congrArg Neg.neg he)
  · rcases griessShortPermutation_vector (generatedFourthMonomialFiber k).val.2
        generatedFourthFlagShort with h | h
    · exact Or.inr (h.symm.trans hn)
    · exact Or.inl (neg_injective (h.symm.trans hn))

/-- All four original word projections lie in the genuine counted physical flag stabilizer. -/
theorem generatedFourth_monomial_flag_mem (k : Fin 4) :
    (generatedFourthMonomialFiber k).val.2 ∈ generatedAxisE8ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort := by
  rw [generatedAxisE8ShortFlagStabilizer_mem]
  exact ⟨generatedAxisE8_preserving_image _ _ (generatedFourth_monomial_section_preserves k),
    generatedFourth_monomial_short_label k⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
