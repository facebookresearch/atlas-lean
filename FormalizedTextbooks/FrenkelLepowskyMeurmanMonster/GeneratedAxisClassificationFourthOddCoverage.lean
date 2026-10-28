/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInputParity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInverseSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddCoefficients

/-! Exhaustive original odd-short support via the bounded input parity test.
The genuine spatial short permutation transports the 120 supported input roots. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A signed physical inverse image gives the exact original integer relation. -/
theorem generatedFourth_inverse_integral_image (r s : GriessShortIndex) (a : ℤ)
    (h : (generatedFourthLocalFiber⁻¹).val.2.val (griessShortVector r) =
      (a : ℝ) • griessShortVector s) :
    generatedFourthInverseNumerator *ᵥ griessShortIntegral r =
      (4 * a) • griessShortIntegral s := by
  change (generatedFourthLocalFiber⁻¹).val.2.val
    (fun i => (griessShortIntegral r i : ℝ) / Real.sqrt 8) = _ at h
  rw [generatedFourth_inverse_normalized_vector] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, griessShortVector] at hi
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  have he : ((generatedFourthInverseNumerator *ᵥ griessShortIntegral r) i : ℝ) =
      4 * (a : ℝ) * (griessShortIntegral s i : ℝ) := by
    field_simp at hi
    nlinarith
  exact_mod_cast he

/-- Every actual odd output has odd forward parity at its actual inverse input. -/
theorem generatedFourth_odd_inverse_input_parity (d : Fin 2048) (i : Fin 24)
    (s : GriessShortIndex) (a : ℤ) (ha : a = 1 ∨ a = -1)
    (h : (generatedFourthLocalFiber⁻¹).val.2.val
        (griessShortVector (Sum.inr (Sum.inr (d, i)))) = (a : ℝ) • griessShortVector s) :
    (generatedFourthInverseNumeratorᵀ *ᵥ griessShortIntegral s) 0 % 8 ≠ 0 := by
  have hv := generatedFourth_inverse_integral_image _ s a h
  have hn := congrArg (fun v => generatedFourthInverseNumeratorᵀ *ᵥ v) hv
  rw [Matrix.mulVec_mulVec, generatedFourth_numerator_transpose_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul] at hn
  have h0 := congrFun hn 0
  simp only [Pi.smul_apply, smul_eq_mul] at h0
  have hu : griessShortIntegral (Sum.inr (Sum.inr (d, i))) 0 = 1 ∨
      griessShortIntegral (Sum.inr (Sum.inr (d, i))) 0 = -1 ∨
      griessShortIntegral (Sum.inr (Sum.inr (d, i))) 0 = 3 ∨
      griessShortIntegral (Sum.inr (Sum.inr (d, i))) 0 = -3 := by
    simp only [griessShortIntegral]
    split_ifs <;> norm_num
  rcases ha with rfl | rfl <;> rcases hu with hu | hu | hu | hu <;> rw [hu] at h0 <;>
    norm_num at h0 <;> omega

/-- An odd root whose inverse lies in the original plane is one of the 56 checked roots. -/
theorem generatedFourth_odd_support_certificate (d : Fin 2048) (i : Fin 24) :
    ((∀ k : Fin 24, Nat.testBit 0xcccc00 k.val = false →
        (generatedFourthInverseNumerator *ᵥ griessShortIntegral (Sum.inr (Sum.inr (d, i)))) k = 0) ↔
      ∃ j : Fin 56, generatedFourthOddRootOutputData j = (d, i)) := by
  let r : GriessShortIndex := Sum.inr (Sum.inr (d, i))
  let s := griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2 r
  have hperm : (generatedFourthLocalFiber⁻¹).val.2.val (griessShortVector r) =
      griessShortVector s ∨
      (generatedFourthLocalFiber⁻¹).val.2.val (griessShortVector r) = -griessShortVector s :=
    griessShortPermutation_vector (generatedFourthLocalFiber⁻¹).val.2 r
  constructor
  · intro hs
    have hsphys : ∀ k : Fin 24, Nat.testBit 0xcccc00 k.val = false →
        (generatedFourthLocalFiber⁻¹).val.2.val (griessShortVector r) k = 0 := by
      intro k hk
      apply (generatedFourth_inverse_short_zero r k).mpr
      exact hs k hk
    have hsup : generatedOctadShortSupport generatedFourthOctad s := by
      apply (generatedOctadShortSupport_iff_physical generatedFourthOctad s).mpr
      rw [generatedFourthOctad_mask]
      rcases hperm with hp | hp
      · simpa only [hp] using hsphys
      · simpa only [hp, Pi.neg_apply, neg_eq_zero] using hsphys
    have hpar : (generatedFourthInverseNumeratorᵀ *ᵥ griessShortIntegral s) 0 % 8 ≠ 0 := by
      rcases hperm with hp | hp
      · exact generatedFourth_odd_inverse_input_parity d i s 1 (Or.inl rfl)
          (by simpa only [Int.cast_one, one_smul] using hp)
      · exact generatedFourth_odd_inverse_input_parity d i s (-1) (Or.inr rfl)
          (by simpa only [Int.cast_neg, Int.cast_one, neg_one_smul] using hp)
    obtain ⟨j, hj⟩ := generatedFourth_supported_input_parity s hsup hpar
    have he : generatedFourthOddRootOutputLabel j = r := by
      apply (griessShortPermutation (generatedFourthLocalFiber⁻¹).val.2).injective
      exact (generatedFourth_odd_inverse_permutation j).trans hj
    refine ⟨j, ?_⟩
    simpa only [generatedFourthOddRootOutputLabel, r, Sum.inr.injEq] using he
  · rintro ⟨j, hj⟩
    have he : generatedFourthOddRootOutputLabel j = r := by
      simp only [generatedFourthOddRootOutputLabel, hj, r]
    have hcoef := generatedFourth_odd_middle_coefficient j
    rw [generatedFourth_local_short] at hcoef
    have hn : localShortOperator generatedFourthLocalFiber
        (griessConwayEncode (sExtra (conwayShortAxis
          (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
            (generatedFourthOddRootOutputLabel j) ≠ 0 := by
      rw [hcoef]
      intro hz
      have hh := qSign_sq (generatedFourthOddCoefficientPhaseData j)
      rw [hz] at hh
      norm_num at hh
    have hsphys := (generatedFourth_transported_short_support generatedFourthLocalFiber
      generatedFourthOctad 0 0 (generatedFourthOddRootOutputLabel j)).mp hn
    rw [generatedFourthOctad_mask, he] at hsphys
    intro k hk
    exact (generatedFourth_inverse_short_zero r k).mp (hsphys k hk)

/-- Exact odd-coordinate support in the genuine local transition. -/
theorem generatedFourth_odd_middle_nonzero_iff (d : Fin 2048) (i : Fin 24) :
    localShortOperator generatedFourthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 (Sum.inr (Sum.inr (d, i))) ≠ 0 ↔
      ∃ j : Fin 56, generatedFourthOddRootOutputData j = (d, i) := by
  rw [generatedFourth_transported_short_support, generatedFourthOctad_mask]
  simp_rw [generatedFourth_inverse_short_zero]
  exact generatedFourth_odd_support_certificate d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
