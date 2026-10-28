/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SliceCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityCoordinates

/-! Actual norm-four roots with small energy outside the physical octad lie in that octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The squared integral coordinates outside the actual enclosing octad. -/
def generatedTenthE7OutsideSquare (u : Fin 24 → ℤ) : ℤ :=
  ∑ i ∈ Finset.univ \ generatedTenthE7OctadSupport, u i ^ 2

/-- Every actual norm-four root with outside square at most eight is supported on the octad. -/
theorem generatedTenth_e7_short_supported_of_outside_bound (u : leechIntegral)
    (hn : leechSquareSum u.val = 32)
    (hout : generatedTenthE7OutsideSquare u.val ≤ 8) :
    ∀ k, k ∉ generatedTenthE7OctadSupport → u.val k = 0 := by
  classical
  let s := Finset.univ \ generatedTenthE7OctadSupport
  have hsum : (∑ i ∈ s, u.val i ^ 2) ≤ 8 := hout
  obtain ⟨z, hz⟩ : ∃ z : Fin 24, u.val z = 0 := by
    by_contra! hzero
    have hge : (16 : ℤ) ≤ ∑ i ∈ s, u.val i ^ 2 := by
      calc
        (16 : ℤ) = ∑ _i ∈ s, (1 : ℤ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast generatedTenth_e7_octad_complement_card.symm
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          have hi := hzero i
          rcases lt_or_gt_of_ne hi with hi | hi <;> nlinarith
    omega
  rcases leechShort_even_shapes u hn z hz with ⟨i, j, hij, hi, hj⟩ |
    ⟨c, hc, hw, hcoord⟩
  · intro k hk
    have hks : k ∈ s := by simp [s, hk]
    have hkb := Finset.single_le_sum (fun t _ => sq_nonneg (u.val t)) hks
    have hisq : u.val i ^ 2 = 16 := by
      rcases Int.natAbs_eq_natAbs_iff.mp (show (u.val i).natAbs = (4 : ℤ).natAbs by
        simpa using hi) with h | h <;> rw [h] <;> norm_num
    have hjsq : u.val j ^ 2 = 16 := by
      rcases Int.natAbs_eq_natAbs_iff.mp (show (u.val j).natAbs = (4 : ℤ).natAbs by
        simpa using hj) with h | h <;> rw [h] <;> norm_num
    have hki : k ≠ i := by intro h; subst k; omega
    have hkj : k ≠ j := by intro h; subst k; omega
    have hthree : (∑ t ∈ ({i, j, k} : Finset (Fin 24)), u.val t ^ 2) ≤
        leechSquareSum u.val := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro t _ _
      exact sq_nonneg _
    have hthree' : u.val i ^ 2 + u.val j ^ 2 + u.val k ^ 2 ≤
        leechSquareSum u.val := by
      simpa [hij, Ne.symm hki, Ne.symm hkj, add_assoc] using hthree
    rw [hn, hisq, hjsq] at hthree'
    nlinarith [sq_nonneg (u.val k)]
  · have hcount : (∑ i ∈ s, (c i).val) ≤ 2 := by
      have he : (∑ i ∈ s, u.val i ^ 2) =
          (4 : ℤ) * ((∑ i ∈ s, (c i).val : ℕ) : ℤ) := by
        rw [Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact hcoord i
      rw [he] at hsum
      omega
    have hdout : (∑ i, if generatedTenthE7OctadWord i = 0 then (c i).val else 0) ≤ 2 := by
      have he : (∑ i, if generatedTenthE7OctadWord i = 0 then (c i).val else 0) =
          ∑ i ∈ s, (c i).val := by
        rw [← Finset.sum_filter]
        congr 1
      exact he.le.trans hcount
    have hcd := generatedTenth_e7_octad_eq_of_outside_weight c generatedTenthE7OctadWord
      hc generatedTenth_e7_octad_mem_code hw generatedTenth_e7_octad_weight hdout
    intro k hk
    have hzcode : c k = 0 := by rw [hcd, generatedTenth_e7_octad_coordinates]; simp [hk]
    have hh := hcoord k
    rw [hzcode] at hh
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero] at hh
    nlinarith [sq_nonneg (u.val k)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
