/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadData

/-! Complete octad-source coverage from the actual physical frame columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 8000000 in
-- Exhaust all genuine physical signed pairs, using the octad coordinate-square pattern.
/-- Every physical pair with octad-shaped image is in the displayed 273-source list. -/
theorem generatedSixth_middle_octad_source_coverage : ∀ s : Fin 2, ∀ i j : Fin 24,
    i < j →
    (∀ x : Fin 24,
      (generatedSixthFrameVectorData 8 i x +
        (if s = 0 then -1 else 1) * generatedSixthFrameVectorData 8 j x) ^ 2 = 0 ∨
      (generatedSixthFrameVectorData 8 i x +
        (if s = 0 then -1 else 1) * generatedSixthFrameVectorData 8 j x) ^ 2 = 16) →
    ∃ k : Fin 273, generatedSixthMiddleOctadSourceCoordinates k = (s, i, j) := by
  decide +kernel

/-- Every genuine source pair reaching an actual octad label is one of the displayed sources. -/
theorem generatedSixth_middle_octad_actual_source (s : Fin 2) (p : Fin 276)
    (o : Fin 759) (e : Fin 64)
    (hp : griessShortPermutation generatedSixthLocalFiber.val.2 (Sum.inl (s, p)) =
      Sum.inr (Sum.inl (o, e))) :
    ∃ k : Fin 273, generatedSixthMiddleOctadInput k = (s, p) := by
  have hl := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hl
  have hpattern (x : Fin 24) :
      (generatedSixthFrameVectorData 8 (griessCoordinatePair p).1 x +
        (if s = 0 then -1 else 1) *
          generatedSixthFrameVectorData 8 (griessCoordinatePair p).2 x) ^ 2 = 0 ∨
      (generatedSixthFrameVectorData 8 (griessCoordinatePair p).1 x +
        (if s = 0 then -1 else 1) *
          generatedSixthFrameVectorData 8 (griessCoordinatePair p).2 x) ^ 2 = 16 := by
    have hv := generatedSixth_short_integral_sign generatedSixthLocalFiber.val.2 (Sum.inl (s,p))
    rw [hp] at hv
    have hs : griessShortIntegral (Sum.inr (Sum.inl (o,e))) x ^ 2 = 0 ∨
        griessShortIntegral (Sum.inr (Sum.inl (o,e))) x ^ 2 = 4 := by
      rw [griessOctad_coordinate_square]
      split_ifs <;> simp
    have hi : (leechIntegralAction generatedSixthLocalFiber.val.2
        (griessShortLatticeVector (Sum.inl (s,p)))).val x ^ 2 = 0 ∨
        (leechIntegralAction generatedSixthLocalFiber.val.2
          (griessShortLatticeVector (Sum.inl (s,p)))).val x ^ 2 = 4 := by
      rcases hv with hv | hv
      · rw [congrFun hv x]
        exact hs
      · rw [congrFun hv x]
        simpa only [Pi.neg_apply, neg_sq] using hs
    have hf := generatedSixth_forward_pair_coordinate s p x
    rw [← hf, mul_pow]
    rcases hi with hi | hi
    · left
      rw [hi, mul_zero]
    · right
      norm_num [hi]
  obtain ⟨k, hk⟩ := generatedSixth_middle_octad_source_coverage s
    (griessCoordinatePair p).1 (griessCoordinatePair p).2 hl hpattern
  refine ⟨k, ?_⟩
  unfold generatedSixthMiddleOctadInput
  simp only [hk]
  congr 1
  exact griessPairIndex_pair p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
