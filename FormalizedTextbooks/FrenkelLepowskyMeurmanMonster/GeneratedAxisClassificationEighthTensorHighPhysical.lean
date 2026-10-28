/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorHighData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthSpatial

/-! The high source pairs have only one possible odd image with exceptional coordinate sixteen. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The exact original forward lattice action, with its denominator cleared. -/
theorem generatedEighth_forward_integral_coordinate (u : leechIntegral) (i : Fin 24) :
    8 * (leechIntegralAction generatedEighthLocalFiber.val.2 u).val i =
      ∑ j, generatedEighthFrameVectorData 7 j i * u.val j := by
  have he := congrFun (leechIntegralAction_embedding generatedEighthLocalFiber.val.2 u) i
  rw [← leechIsomMatrix_mulVec generatedEighthLocalFiber.val.2] at he
  change (((leechIntegralAction generatedEighthLocalFiber.val.2 u).val i : ℤ) : ℝ) /
      Real.sqrt 8 = (∑ j, leechIsomMatrix generatedEighthLocalFiber.val.2 i j *
        ((u.val j : ℝ) / Real.sqrt 8)) at he
  simp_rw [generatedEighth_forward_matrix_coordinate, div_mul_div_comm] at he
  rw [← Finset.sum_div] at he
  have hs : Real.sqrt 8 ≠ 0 := by positivity
  field_simp [hs] at he
  have hi : (leechIntegralAction generatedEighthLocalFiber.val.2 u).val i * 8 =
      ∑ j, generatedEighthFrameVectorData 7 j i * u.val j := by exact_mod_cast he
  simpa only [mul_comm] using hi

/-- The forward image of each original pair has the exact sum or difference of two frame columns. -/
theorem generatedEighth_forward_pair_coordinate (s : Fin 2) (p : Fin 276) (i : Fin 24) :
    2 * (leechIntegralAction generatedEighthLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (s, p)))).val i =
      generatedEighthFrameVectorData 7 (griessCoordinatePair p).1 i +
      (if s = 0 then -1 else 1) *
        generatedEighthFrameVectorData 7 (griessCoordinatePair p).2 i := by
  have h := generatedEighth_forward_integral_coordinate
    (griessShortLatticeVector (Sum.inl (s, p))) i
  change 8 * _ = ∑ j, generatedEighthFrameVectorData 7 j i *
    griessShortIntegral (Sum.inl (s, p)) j at h
  simp only [griessShortIntegral, mul_add, Finset.sum_add_distrib,
    mul_ite, mul_zero] at h
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq'] at h
  simp only [Finset.mem_univ, ite_true] at h
  split_ifs at h ⊢ <;> omega

/-- Every selected source has the exact signed actual integral image. -/
theorem generatedEighth_high_integral_image (j : Fin 12) :
    (leechIntegralAction generatedEighthLocalFiber.val.2
      (griessShortLatticeVector (generatedEighthHighSource j))).val =
        fun i => generatedEighthHighPhysicalSign j *
          griessShortIntegral (generatedEighthHighTarget j) i := by
  funext i
  simp only [generatedEighthHighSource]
  have h := generatedEighth_forward_pair_coordinate
    (generatedEighthHighSourceCoordinates j).1 (generatedEighthHighSourcePair j) i
  rw [generatedEighth_high_source_coordinates] at h
  rw [generatedEighth_high_physical_certificate] at h
  change _ = generatedEighthHighPhysicalSign j *
    griessShortIntegral (generatedEighthHighTarget j) i
  exact Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0)
    (by simpa only [mul_assoc] using h)

/-- The physical integer certificate gives the genuine normalized vector image. -/
theorem generatedEighth_high_vector_image (j : Fin 12) :
    generatedEighthLocalFiber.val.2.val (griessShortVector (generatedEighthHighSource j)) =
      (generatedEighthHighPhysicalSign j : ℝ) •
        griessShortVector (generatedEighthHighTarget j) := by
  have h := leechIntegralAction_embedding generatedEighthLocalFiber.val.2
    (griessShortLatticeVector (generatedEighthHighSource j))
  funext i
  have hi := congrFun h i
  change (((leechIntegralAction generatedEighthLocalFiber.val.2
    (griessShortLatticeVector (generatedEighthHighSource j))).val i : ℝ) / Real.sqrt 8) =
      generatedEighthLocalFiber.val.2.val
        (griessShortVector (generatedEighthHighSource j)) i at hi
  rw [congrFun (generatedEighth_high_integral_image j) i] at hi
  simp only [Int.cast_mul] at hi
  change _ = (generatedEighthHighPhysicalSign j : ℝ) *
    ((griessShortIntegral (generatedEighthHighTarget j) i : ℝ) / Real.sqrt 8)
  rw [← hi]
  ring

private theorem physical_sign_cases : ∀ j : Fin 12,
    generatedEighthHighPhysicalSign j = 1 ∨ generatedEighthHighPhysicalSign j = -1 := by
  decide +kernel

/-- The selected source reaches its actual odd catalogue label, with no spin-sign assumption. -/
theorem generatedEighth_high_permutation (j : Fin 12) :
    griessShortPermutation generatedEighthLocalFiber.val.2 (generatedEighthHighSource j) =
      generatedEighthHighTarget j := by
  have hv := generatedEighth_high_vector_image j
  have hv' : generatedEighthLocalFiber.val.2.val
      (griessShortVector (generatedEighthHighSource j)) =
        griessShortVector (generatedEighthHighTarget j) ∨
      generatedEighthLocalFiber.val.2.val (griessShortVector (generatedEighthHighSource j)) =
        -griessShortVector (generatedEighthHighTarget j) := by
    rcases physical_sign_cases j with hs | hs
    · left
      simpa only [hs, Int.cast_one, one_smul] using hv
    · right
      simpa only [hs, Int.cast_neg, Int.cast_one, neg_one_smul] using hv
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector generatedEighthLocalFiber.val.2
    (generatedEighthHighSource j) with hp | hp
  · rcases hv' with hv' | hv'
    · exact Or.inl (hp.symm.trans hv')
    · exact Or.inr (hp.symm.trans hv')
  · rcases hv' with hv' | hv'
    · right
      have he := congrArg Neg.neg (hp.symm.trans hv')
      simpa only [neg_neg] using he
    · exact Or.inl (neg_injective (hp.symm.trans hv'))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
