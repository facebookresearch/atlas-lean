/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhHighPairCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatial

/-! The high source pairs have only one possible odd image with exceptional coordinate sixteen. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The exact original forward lattice action, with its denominator cleared. -/
theorem generatedSeventh_forward_integral_coordinate (u : leechIntegral) (i : Fin 24) :
    8 * (leechIntegralAction generatedSeventhLocalFiber.val.2 u).val i =
      ∑ j, generatedSeventhFrameVectorData 7 j i * u.val j := by
  have he := congrFun (leechIntegralAction_embedding generatedSeventhLocalFiber.val.2 u) i
  rw [← leechIsomMatrix_mulVec generatedSeventhLocalFiber.val.2] at he
  change (((leechIntegralAction generatedSeventhLocalFiber.val.2 u).val i : ℤ) : ℝ) /
      Real.sqrt 8 = (∑ j, leechIsomMatrix generatedSeventhLocalFiber.val.2 i j *
        ((u.val j : ℝ) / Real.sqrt 8)) at he
  simp_rw [generatedSeventh_forward_matrix_coordinate, div_mul_div_comm] at he
  rw [← Finset.sum_div] at he
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hs] at he
  have hi : (leechIntegralAction generatedSeventhLocalFiber.val.2 u).val i * 8 =
      ∑ j, generatedSeventhFrameVectorData 7 j i * u.val j := by exact_mod_cast he
  simpa only [mul_comm] using hi

/-- The forward image of each original pair has the exact sum or difference of two frame columns. -/
theorem generatedSeventh_forward_pair_coordinate (s : Fin 2) (p : Fin 276) (i : Fin 24) :
    2 * (leechIntegralAction generatedSeventhLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (s, p)))).val i =
      generatedSeventhFrameVectorData 7 (griessCoordinatePair p).1 i +
      (if s = 0 then -1 else 1) *
        generatedSeventhFrameVectorData 7 (griessCoordinatePair p).2 i := by
  have h := generatedSeventh_forward_integral_coordinate
    (griessShortLatticeVector (Sum.inl (s, p))) i
  change 8 * _ = ∑ j, generatedSeventhFrameVectorData 7 j i *
    griessShortIntegral (Sum.inl (s, p)) j at h
  simp only [griessShortIntegral, mul_add, Finset.sum_add_distrib,
    mul_ite, mul_zero] at h
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq'] at h
  simp only [Finset.mem_univ, ite_true] at h
  split_ifs at h ⊢ <;> omega

/-- The forty-six original high pairs have a unique odd image distinguished at sixteen. -/
theorem generatedSeventh_high_pair_sixteen_certificate : ∀ s : Fin 2, ∀ k : Fin 24,
    k ≠ 0 →
    (generatedSeventhFrameVectorData 7 0 16 + (if s = 0 then -1 else 1) *
      generatedSeventhFrameVectorData 7 k 16) ^ 2 = 36 → s = 1 ∧ k = 12 := by
  decide +kernel

/-- A high pair reaching an odd label distinguished at sixteen is the plus pair zero/twelve. -/
theorem generatedSeventh_high_odd_sixteen_source (s : Fin 2) (p : Fin 276) (d : Fin 2048)
    (ha : (griessCoordinatePair p).1 = 0)
    (hp : griessShortPermutation generatedSeventhLocalFiber.val.2 (Sum.inl (s, p)) =
      Sum.inr (Sum.inr (d, 16))) :
    s = 1 ∧ (griessCoordinatePair p).2 = 12 := by
  have hn : (griessCoordinatePair p).2 ≠ 0 := by
    intro hn
    exact griessCoordinatePair_ne p (ha.trans hn.symm)
  have hf := generatedSeventh_forward_pair_coordinate s p 16
  have hv := generatedSeventh_short_integral_sign generatedSeventhLocalFiber.val.2 (Sum.inl (s, p))
  rw [hp] at hv
  have hs : griessShortIntegral (Sum.inr (Sum.inr (d, 16))) 16 ^ 2 = 9 := by
    rw [griessOdd_coordinate_square]
    simp only [ite_true]
  have hz : (leechIntegralAction generatedSeventhLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (s, p)))).val 16 ^ 2 = 9 := by
    rcases hv with hv | hv
    · rw [congrFun hv 16]
      exact hs
    · change _ = fun i => -griessShortIntegral (Sum.inr (Sum.inr (d, 16))) i at hv
      rw [congrFun hv 16, neg_sq]
      exact hs
  apply generatedSeventh_high_pair_sixteen_certificate s (griessCoordinatePair p).2 hn
  rw [ha] at hf
  rw [← hf, mul_pow, hz]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
