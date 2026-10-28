/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorSquares

/-! The original forward coordinates completely classify all high odd rows in column twenty. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- Check all forty-six original high source pairs against the twelve actual source addresses.
/-- Every original high pair with odd exceptional coordinate twenty is on the exact source list. -/
theorem generatedEighth_high_pair_twenty_certificate : ∀ s : Fin 2, ∀ k : Fin 24,
    k ≠ 0 →
    (generatedEighthFrameVectorData 7 0 20 + (if s = 0 then -1 else 1) *
      generatedEighthFrameVectorData 7 k 20) ^ 2 = 36 →
    ∃ j : Fin 12, generatedEighthHighSourceCoordinates j = (s, k) := by
  decide +kernel

/-- Every high original pair reaching an odd row in column twenty has its actual listed label. -/
theorem generatedEighth_high_odd_source (s : Fin 2) (p : Fin 276) (d : Fin 2048)
    (ha : (griessCoordinatePair p).1 = 0)
    (hp : griessShortPermutation generatedEighthLocalFiber.val.2 (Sum.inl (s, p)) =
      Sum.inr (Sum.inr (d, 20))) :
    ∃ j : Fin 12, generatedEighthHighSource j = Sum.inl (s, p) ∧
      generatedEighthHighOddCode j = d := by
  have hn : (griessCoordinatePair p).2 ≠ 0 := by
    intro hn
    exact griessCoordinatePair_ne p (ha.trans hn.symm)
  have hf := generatedEighth_forward_pair_coordinate s p 20
  have hv := generatedSixth_short_integral_sign generatedEighthLocalFiber.val.2
    (Sum.inl (s, p))
  rw [hp] at hv
  have hs : griessShortIntegral (Sum.inr (Sum.inr (d, 20))) 20 ^ 2 = 9 := by
    rw [griessOdd_coordinate_square]
    simp only [ite_true]
  have hz : (leechIntegralAction generatedEighthLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (s, p)))).val 20 ^ 2 = 9 := by
    rcases hv with hv | hv
    · rw [congrFun hv 20]
      exact hs
    · change _ = fun i => -griessShortIntegral (Sum.inr (Sum.inr (d, 20))) i at hv
      rw [congrFun hv 20, neg_sq]
      exact hs
  have he : (generatedEighthFrameVectorData 7 0 20 + (if s = 0 then -1 else 1) *
      generatedEighthFrameVectorData 7 (griessCoordinatePair p).2 20) ^ 2 = 36 := by
    rw [ha] at hf
    rw [← hf, mul_pow, hz]
    norm_num
  obtain ⟨j, hj⟩ := generatedEighth_high_pair_twenty_certificate s
    (griessCoordinatePair p).2 hn he
  have hpair : generatedEighthHighSourcePair j = p := by
    apply griessCoordinatePairEquiv.injective
    apply Subtype.ext
    change griessCoordinatePair (generatedEighthHighSourcePair j) = griessCoordinatePair p
    rw [generatedEighth_high_source_coordinates, hj]
    apply Prod.ext
    · exact ha.symm
    · rfl
  have hsource : generatedEighthHighSource j = Sum.inl (s, p) := by
    simp only [generatedEighthHighSource, hj, hpair]
  have hi := generatedEighth_high_permutation j
  rw [hsource, hp] at hi
  change Sum.inr (Sum.inr (d, (20 : Fin 24))) =
    Sum.inr (Sum.inr (generatedEighthHighOddCode j, (20 : Fin 24))) at hi
  exact ⟨j, hsource, (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj hi))).1.symm⟩

private theorem short_square (f : localFiberSubgroup) (X : GriessShortIndex → ℝ)
    (r : GriessShortIndex) :
    (localShortOperator f X r) ^ 2 =
      (X ((griessShortPermutation f.val.2).symm r)) ^ 2 := by
  change (qSign _ * X _) ^ 2 = _
  rw [mul_pow, pow_two (qSign _), qSign_sq, one_mul]

private theorem coordinate_pair_lt (p : Fin 276) :
    (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
  (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2

/-- Every actual odd row outside the twelve-code list has only the original small-quarter bound. -/
theorem generatedEighth_middle_odd_small (d : Fin 2048)
    (hd : ∀ j : Fin 12, d ≠ generatedEighthHighOddCode j) :
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (d, 20)))) ^ 2 ≤ (1 / 16 : ℝ) := by
  rw [generatedFourth_local_short, short_square]
  let r := (griessShortPermutation generatedEighthLocalFiber.val.2).symm
    (Sum.inr (Sum.inr (d, 20)))
  change ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 ≤ _
  have hi : griessShortPermutation generatedEighthLocalFiber.val.2 r =
      Sum.inr (Sum.inr (d, 20)) := Equiv.apply_symm_apply _ _
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨c, j⟩
  · have ha : (griessCoordinatePair p).1 ≠ 0 := by
      intro ha
      obtain ⟨k, _, hk⟩ := generatedEighth_high_odd_source s p d ha hi
      exact hd k hk.symm
    have hb : (griessCoordinatePair p).2 ≠ 0 := by
      have hl := coordinate_pair_lt p
      intro hb
      rw [hb] at hl
      omega
    rw [generatedSixth_original_pair_small s p ha hb]
  · rw [show (griessConwayEncode generatedOddAxis).2.1
        (Sum.inr (Sum.inl (o, e))) = 0 from
        generatedAxis_triality_odd_octad_coordinate 0 0 0 o e]
    norm_num
  · rw [show (griessConwayEncode generatedOddAxis).2.1
        (Sum.inr (Sum.inr (c, j))) = 0 from
        generatedAxis_triality_odd_odd_coordinate 0 c 0 j 0]
    norm_num

/-- Outside the actual high-code list, the original tensor square is at most one hundred. -/
theorem generatedEighth_tensor_column_small (t : SpinIndex)
    (ht : ∀ j : Fin 12, spinDictionaryCode t ≠ generatedEighthHighOddCode j) :
    (generatedEighthTensorColumn t) ^ 2 ≤ 100 := by
  have hx : (generatedEighthTensorXContribution t) ^ 2 ≤ 64 := by
    rw [generatedEighth_tensor_X_square]
    have h := generatedEighth_middle_odd_small (spinDictionaryCode t) ht
    linarith
  have hy := generatedEighth_tensor_Y_twenty_square t
  have hxl : -8 ≤ generatedEighthTensorXContribution t := by nlinarith only [hx]
  have hxu : generatedEighthTensorXContribution t ≤ 8 := by nlinarith only [hx]
  have hyl : -2 ≤ generatedEighthTensorYContribution t 20 := by nlinarith only [hy]
  have hyu : generatedEighthTensorYContribution t 20 ≤ 2 := by nlinarith only [hy]
  rw [generatedEighth_tensor_column_coordinate]
  nlinarith only [hxl, hxu, hyl, hyu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
