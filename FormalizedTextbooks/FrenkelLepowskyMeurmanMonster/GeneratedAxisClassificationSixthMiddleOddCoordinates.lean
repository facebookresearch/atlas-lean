/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddData

/-! The finite physical odd images are the actual original short permutation labels. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every displayed physical image sign is one or minus one. -/
theorem generatedSixth_middle_odd_physical_sign (k : Fin 276) :
    generatedSixthMiddleOddPhysicalSign k = 1 ∨ generatedSixthMiddleOddPhysicalSign k = -1 := by
  revert k
  decide +kernel

/-- The genuine original integral action realizes each verified physical target. -/
theorem generatedSixth_middle_odd_integral_image (k : Fin 276) :
    (leechIntegralAction generatedSixthLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (generatedSixthMiddleOddInput k)))).val =
      fun i => generatedSixthMiddleOddPhysicalSign k *
        griessShortIntegral (generatedSixthMiddleOddOutput k) i := by
  funext i
  have hf := generatedSixth_forward_pair_coordinate
    (generatedSixthMiddleOddInput k).1 (generatedSixthMiddleOddInput k).2 i
  unfold generatedSixthMiddleOddInput at hf
  rw [griessPairIndex_coordinates,
    ite_eq_left (generatedSixth_middle_odd_source_lt k)] at hf
  have hc := generatedSixth_middle_odd_physical_certificate k i
  rw [hc] at hf
  change 2 * (leechIntegralAction generatedSixthLocalFiber.val.2
    (griessShortLatticeVector (Sum.inl (generatedSixthMiddleOddInput k)))).val i =
      2 * generatedSixthMiddleOddPhysicalSign k *
        griessShortIntegral (generatedSixthMiddleOddOutput k) i at hf
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  simpa only [mul_assoc] using hf

/-- Equality of signed actual integral short images identifies the genuine catalogue label. -/
theorem generatedSixth_short_label_of_integral_image (e : leechIsomSubgroup)
    (r s : GriessShortIndex)
    (h : (leechIntegralAction e (griessShortLatticeVector r)).val = griessShortIntegral s ∨
      (leechIntegralAction e (griessShortLatticeVector r)).val = -griessShortIntegral s) :
    griessShortPermutation e r = s := by
  have hv := generatedSixth_short_integral_sign e r
  apply griessShort_label_unique
  rcases hv with hv | hv <;> rcases h with h | h
  · exact Or.inl (hv.symm.trans h)
  · exact Or.inr (hv.symm.trans h)
  · right
    simpa only [neg_neg] using congrArg Neg.neg (hv.symm.trans h)
  · left
    simpa only [neg_neg] using congrArg Neg.neg (hv.symm.trans h)

/-- Each displayed odd target is the actual preferred-short permutation image. -/
theorem generatedSixth_middle_odd_permutation (k : Fin 276) :
    generatedSixthMiddleShortLabel (generatedSixthMiddleOddInput k) =
      generatedSixthMiddleOddOutput k := by
  apply generatedSixth_short_label_of_integral_image
  have h := generatedSixth_middle_odd_integral_image k
  rcases generatedSixth_middle_odd_physical_sign k with hs | hs
  · left
    simpa only [hs, one_mul] using h
  · right
    change (leechIntegralAction generatedSixthLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (generatedSixthMiddleOddInput k)))).val =
        fun i => -griessShortIntegral (generatedSixthMiddleOddOutput k) i
    simpa only [hs, neg_one_mul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
