/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddData

/-! Every actual middle odd-short coordinate comes from
the displayed genuine physical source list. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Exhaust the finite physical signed-pair carrier, without assigning numeric catalogue indices.
/-- A physical pair image with no zero coordinate occurs in the complete odd-source list. -/
theorem generatedSixth_middle_odd_source_coverage : ∀ s : Fin 2, ∀ i j : Fin 24,
    i < j →
    (∀ x : Fin 24, generatedSixthFrameVectorData 8 i x +
      (if s = 0 then -1 else 1) * generatedSixthFrameVectorData 8 j x ≠ 0) →
    ∃ k : Fin 276, generatedSixthMiddleOddSourceCoordinates k = (s, i, j) := by
  decide +kernel

/-- Every genuine pair reaching an odd short coordinate is one of the displayed physical sources. -/
theorem generatedSixth_middle_odd_actual_source (s : Fin 2) (p : Fin 276)
    (d : Fin 2048) (j : Fin 24)
    (hp : griessShortPermutation generatedSixthLocalFiber.val.2 (Sum.inl (s, p)) =
      Sum.inr (Sum.inr (d, j))) :
    ∃ k : Fin 276, generatedSixthMiddleOddInput k = (s, p) := by
  have hl := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hl
  have hn (x : Fin 24) :
      (leechIntegralAction generatedSixthLocalFiber.val.2
        (griessShortLatticeVector (Sum.inl (s, p)))).val x ≠ 0 := by
    have hv := generatedSixth_short_integral_sign generatedSixthLocalFiber.val.2
      (Sum.inl (s, p))
    rw [hp] at hv
    have hs := griessOdd_coordinate_square d j x
    have hz : griessShortIntegral (Sum.inr (Sum.inr (d, j))) x ≠ 0 := by
      split_ifs at hs <;> nlinarith
    rcases hv with hv | hv
    · rw [congrFun hv x]
      exact hz
    · change _ = fun x => -griessShortIntegral (Sum.inr (Sum.inr (d, j))) x at hv
      rw [congrFun hv x]
      exact neg_ne_zero.mpr hz
  obtain ⟨k, hk⟩ := generatedSixth_middle_odd_source_coverage s
    (griessCoordinatePair p).1 (griessCoordinatePair p).2 hl (fun x hx => by
      have he := generatedSixth_forward_pair_coordinate s p x
      rw [hx] at he
      exact hn x (by omega))
  refine ⟨k, ?_⟩
  unfold generatedSixthMiddleOddInput
  simp only [hk]
  congr 1
  exact griessPairIndex_pair p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
