/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInputEnumeration

/-! Complete actual 120-root support of the local middle word, obtained by transporting
an exhaustive finite input enumeration with the genuine preferred-short permutation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The sole pair output has the exact original preferred pair inverse image. -/
theorem generatedFourth_pair_inverse_vector :
    (generatedFourthLocalFiber⁻¹).val.2.val (griessShortVector generatedFourthPairInput) =
      griessShortVector generatedFourthPairOutput := by
  have hc : ∀ i : Fin 24,
      (generatedFourthInverseNumerator *ᵥ griessShortIntegral generatedFourthPairInput) i =
        4 * griessShortIntegral generatedFourthPairOutput i := by
    simp only [generatedFourthPairInput, generatedFourthPairOutput, griessShortIntegral,
      griessPairIndex_coordinates, show (8 : Fin 24) < 11 from by decide,
      show (10 : Fin 24) < 11 from by decide, ite_true]
    decide +kernel
  change (generatedFourthLocalFiber⁻¹).val.2.val
    (fun i => (griessShortIntegral generatedFourthPairInput i : ℝ) / Real.sqrt 8) = _
  rw [generatedFourth_inverse_normalized_vector]
  funext i
  rw [hc i]
  simp only [griessShortVector, Int.cast_mul, Int.cast_ofNat]
  ring

/-- The actual inverse preferred-short permutation sends the sole pair output to its input. -/
theorem generatedFourth_pair_inverse_permutation :
    griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2 generatedFourthPairInput =
      generatedFourthPairOutput := by
  have h := generatedFourth_pair_inverse_vector
  rcases griessShortPermutation_vector (generatedFourthLocalFiber⁻¹).val.2
    generatedFourthPairInput with hv | hv
  · exact centralizer_shortVector_line_unique _ _ (1 : ℝ) (by
      simpa only [one_smul] using hv.symm.trans h)
  · exact centralizer_shortVector_line_unique _ _ (-1 : ℝ) (by
      simpa only [neg_one_smul, Pi.neg_apply, neg_neg] using
        congrArg Neg.neg (hv.symm.trans h))

/-- Every nonzero actual middle short coordinate is one of the certified 120 output labels. -/
theorem generatedFourth_middle_support_enumeration (r : GriessShortIndex)
    (hr : localShortOperator generatedFourthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 r ≠ 0) :
    (∃ j : Fin 56, generatedFourthOddRootOutputLabel j = r) ∨
      (∃ j : Fin 63, generatedFourthEvenRootOutputLabel j = r) ∨
        generatedFourthPairInput = r := by
  let s := (griessShortPermutation generatedFourthLocalFiber.val.2).symm r
  have hn : (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 s ≠ 0 :=
    (mul_ne_zero_iff.mp hr).2
  have hs : generatedOctadShortSupport generatedFourthOctad s :=
    (generatedAxis_triality_octad_support_iff generatedFourthOctad 0 0 s).mp hn
  have hp : griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2 r = s := by
    change griessShortPermutation (generatedFourthLocalFiber.val.2⁻¹) r = s
    rw [map_inv]
    rfl
  rcases generatedFourth_supported_input_enumeration s hs with ⟨j, hj⟩ | ⟨j, hj⟩ | hj
  · left
    refine ⟨j, ?_⟩
    apply (griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2).injective
    rw [generatedFourth_odd_inverse_permutation, hj, hp]
  · right; left
    refine ⟨j, ?_⟩
    apply (griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2).injective
    rw [generatedFourth_even_inverse_permutation, hj, hp]
  · right; right
    apply (griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2).injective
    rw [generatedFourth_pair_inverse_permutation, hj, hp]

/-- Every actual middle octad coordinate outside the 63 certified labels is zero. -/
theorem generatedFourth_middle_octad_zero_outside (o : Fin 759) (e : Fin 64)
    (h : ¬∃ j : Fin 63,
      generatedFourthEvenRootOutputLabel j = Sum.inr (Sum.inl (o, e))) :
    localShortOperator generatedFourthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 (Sum.inr (Sum.inl (o, e))) = 0 := by
  by_contra hn
  rcases generatedFourth_middle_support_enumeration _ hn with ⟨j, hj⟩ | hj | hj
  · simp only [generatedFourthOddRootOutputLabel, Sum.inr.injEq, reduceCtorEq] at hj
  · exact h hj
  · simp only [generatedFourthPairInput, reduceCtorEq] at hj

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
