/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.Periodic.BinaryRecurrenceRealizableDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

open Function

namespace MathlibExtTest.Dynamics.Periodic.BinaryRecurrenceRealizableDimension

private noncomputable def realizableDim (B C : ℤ) : ℕ :=
  Module.finrank ℂ ↥(Submodule.span ℂ
    {w : ℕ → ℂ | ∃ u : ℕ → ℤ,
      (∀ n : ℕ, u (n + 2) = B * u (n + 1) - C * u n) ∧
      (∃ (X : Type) (T : X → X),
        ∀ n : ℕ, ∃ S : Set X, S = {x | T^[n + 1] x = x} ∧ S.Finite ∧
          S.ncard = (u n).natAbs) ∧
      w = fun n => (u n : ℂ)})

private theorem distinct_roots {B C a b : ℂ}
    (ha : a ^ 2 - B * a + C = 0) (hb : b ^ 2 - B * b + C = 0) (hne : a ≠ b) :
    a + b = B ∧ a * b = C := by
  have hsum : a + b = B := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
    linear_combination ha - hb
  exact ⟨hsum, by linear_combination a * hsum - ha⟩

private theorem ratio_pow_ne_one_of_norm_ne {a b : ℂ} (hb : b ≠ 0)
    (h : ‖a‖ ≠ ‖b‖) (n : ℕ) (hn : 0 < n) : (a / b) ^ n ≠ 1 := by
  intro he
  have hp := congrArg norm he
  rw [norm_pow, norm_one] at hp
  have hnorm := (pow_left_inj₀ (norm_nonneg (a / b)) zero_le_one hn.ne').mp
    (hp.trans (one_pow n).symm)
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hb)] at hnorm
  exact h hnorm

private theorem nondeg_of_roots {B C r s : ℂ} (hC : C ≠ 0)
    (hsum : r + s = B) (hprod : r * s = C) (hnorm : ‖r‖ ≠ ‖s‖)
    (a b : ℂ) (ha : a ^ 2 - B * a + C = 0) (hb : b ^ 2 - B * b + C = 0)
    (hab : a ≠ b) (n : ℕ) (hn : 0 < n) : (a / b) ^ n ≠ 1 := by
  have roots (x : ℂ) (hx : x ^ 2 - B * x + C = 0) : x = r ∨ x = s := by
    have hm : (x - r) * (x - s) = 0 := by linear_combination hx - x * hsum + hprod
    exact (mul_eq_zero.mp hm).imp sub_eq_zero.mp sub_eq_zero.mp
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb; exact hC hb
  apply ratio_pow_ne_one_of_norm_ne hb0 _ n hn
  rcases roots a ha with rfl | rfl <;> rcases roots b hb with rfl | rfl
  · exact (hab rfl).elim
  · exact hnorm
  · exact hnorm.symm
  · exact (hab rfl).elim

-- The repeated root is negative, so the realization uses absolute values.
example : realizableDim (-2) 1 = 1 := by
  have h := MetaMathlibExt.binaryrec_realizable_subspace_dim (-2) 1 (by norm_num) ?_
  · exact h.2.1 (Or.inl (by norm_num))
  · intro a b ha hb hne _ _
    exfalso
    apply hne
    have hroot (x : ℂ) (hx : x ^ 2 - ((-2 : ℤ) : ℂ) * x + 1 = 0) : x = -1 := by
      have he : (x + 1) ^ 2 = 0 := by push_cast at hx; linear_combination hx
      apply eq_neg_of_add_eq_zero_left
      by_contra hn
      exact pow_ne_zero 2 hn he
    exact (hroot a (by simpa using ha)).trans (hroot b (by simpa using hb)).symm

-- A split recurrence with roots 1 and 2 gives two independent realizations.
example : realizableDim 3 2 = 2 := by
  have h := MetaMathlibExt.binaryrec_realizable_subspace_dim 3 2 (by norm_num)
    (nondeg_of_roots (r := 1) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  exact h.2.2 ⟨by norm_num, ⟨1, by norm_num⟩⟩

-- The Fibonacci recurrence has a positive nonsquare discriminant.
example : realizableDim 1 (-1) = 1 := by
  let t := Real.sqrt 5
  let r := (1 + t) / 2
  let s := (1 - t) / 2
  have ht : 1 < t := Real.lt_sqrt_of_sq_lt (by norm_num)
  have ht2 : t ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsum : r + s = 1 := by dsimp [r, s]; ring
  have hprod : r * s = -1 := by dsimp [r, s]; nlinarith
  have habs : |r| ≠ |s| := by
    have hr : 0 < r := by dsimp [r]; linarith
    have hs : s < 0 := by dsimp [s]; linarith
    rw [abs_of_pos hr, abs_of_neg hs]
    linarith
  have h := MetaMathlibExt.binaryrec_realizable_subspace_dim 1 (-1) (by norm_num)
    (nondeg_of_roots (r := r) (s := s) (by norm_num) (by exact_mod_cast hsum)
      (by exact_mod_cast hprod) (by simpa using habs))
  exact h.2.1 (Or.inr ⟨by norm_num, by norm_num⟩)

-- For the discriminant -7, the sum of the root ratio and its inverse is -3/2.
-- A root of unity would make that rational number an algebraic integer.
example : realizableDim 1 2 = 0 := by
  have h := MetaMathlibExt.binaryrec_realizable_subspace_dim 1 2 (by norm_num) ?_
  · exact h.1 (by norm_num)
  · intro a b ha hb hne n hn he
    obtain ⟨hsum, hprod⟩ := distinct_roots ha hb hne
    have hab : a * b = 2 := by simpa using hprod
    have hsum' : a + b = 1 := by simpa using hsum
    have ha0 : a ≠ 0 := by rintro rfl; norm_num at hab
    have hb0 : b ≠ 0 := by rintro rfl; norm_num at hab
    have hrev : (b / a) ^ n = 1 := by rw [← inv_div, inv_pow, he, inv_one]
    have hi : IsIntegral ℤ (a / b + b / a) :=
      (IsIntegral.of_pow hn (he ▸ isIntegral_one)).add
        (IsIntegral.of_pow hn (hrev ▸ isIntegral_one))
    have heq : a / b + b / a = ((-3 / 2 : ℚ) : ℂ) := by
      push_cast
      field_simp
      linear_combination 2 * ((a + b) + 1) * hsum' - hab
    rw [heq] at hi
    obtain ⟨z, hz⟩ := hi.mem_range_ratCast_iff.mp ⟨-3 / 2, rfl⟩
    have hzq : (z : ℚ) = -3 / 2 := by exact_mod_cast hz
    have hzi : 2 * z = -3 := by exact_mod_cast (show (2 : ℚ) * z = -3 by linarith)
    omega

end MathlibExtTest.Dynamics.Periodic.BinaryRecurrenceRealizableDimension
