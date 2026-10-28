/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthHighOddBinding

/-! All other odd coefficients in middle column sixteen have the small quarter bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem short_square (f : localFiberSubgroup) (X : GriessShortIndex → ℝ)
    (r : GriessShortIndex) :
    (localShortOperator f X r) ^ 2 =
      (X ((griessShortPermutation f.val.2).symm r)) ^ 2 := by
  change (qSign _ * X _) ^ 2 = _
  rw [mul_pow, pow_two (qSign _), qSign_sq, one_mul]

/-- Every actual middle short coefficient has the original high-quarter bound. -/
theorem generatedSixth_middle_short_square_bound (r : GriessShortIndex) :
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1 r) ^ 2 ≤
        (9 / 16 : ℝ) := by
  rw [generatedFourth_local_short, short_square]
  exact generatedSixth_original_short_square_bound _

private theorem coordinate_pair_lt (p : Fin 276) :
    (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
  (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2

private theorem source_pair_eq (p : Fin 276)
    (hp : griessCoordinatePair p = (0, 16)) : p = generatedSixthSourcePair 2 := by
  apply griessCoordinatePairEquiv.injective
  apply Subtype.ext
  change griessCoordinatePair p = griessCoordinatePair (generatedSixthSourcePair 2)
  exact hp.trans (generatedSixth_pair_coordinate_certificate 2).1.symm

/-- Only odd code 1010 can exceed the small-quarter bound in middle column sixteen. -/
theorem generatedSixth_middle_odd_sixteen_small (d : Fin 2048) (hd : d ≠ 1010) :
    ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (d, 16)))) ^ 2 ≤ (1 / 16 : ℝ) := by
  rw [generatedFourth_local_short, short_square]
  let r := (griessShortPermutation generatedSixthLocalFiber.val.2).symm
    (Sum.inr (Sum.inr (d, 16)))
  change ((griessConwayEncode generatedOddAxis).2.1 r) ^ 2 ≤ _
  have hi : griessShortPermutation generatedSixthLocalFiber.val.2 r =
      Sum.inr (Sum.inr (d, 16)) := Equiv.apply_symm_apply _ _
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨c, j⟩
  · have ha : (griessCoordinatePair p).1 ≠ 0 := by
      intro ha
      obtain ⟨hs, hb⟩ := generatedSixth_high_odd_sixteen_source s p d ha hi
      have hp := source_pair_eq p (Prod.ext ha hb)
      subst s
      subst p
      rw [generatedSixth_high_odd_permutation] at hi
      have he : (1010 : Fin 2048) = d := by
        exact (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj hi))).1
      exact hd he.symm
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

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
