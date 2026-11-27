/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.KPellLucasCloseToPowerOfTwo
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Tests for `MathlibExt.NumberTheory.KPellLucasCloseToPowerOfTwo` -/

namespace MathlibExtTest.KPellLucasCloseToPowerOfTwo

open MetaMathlibExt

-- At order one the sum of earlier terms is empty, so each term after index one doubles.
example (n : ℕ) : kPellLucas 1 (n + 2) = 2 * kPellLucas 1 (n + 1) := by
  simpa using kPellLucas_add_two 1 n (by omega)

-- At the least allowed order and index, Q₃ = 14 lies two units below 2⁴.
example : (0.69 : ℝ) * 3 - 1.69 < 4 ∧ (4 : ℝ) < 1.39 * 3 + 3.78 := by
  apply kPellLucas_close_two_pow_exponent_bounds 2 3 4 (by decide) (by decide)
    (by decide) (by decide)
  rw [kPellLucas_two]
  norm_num [pellLucas]

-- The next term is above 2⁵, so the opposite side of the interval and an odd exponent occur.
example : (0.69 : ℝ) * 4 - 1.69 < 5 ∧ (5 : ℝ) < 1.39 * 4 + 3.78 := by
  apply kPellLucas_close_two_pow_exponent_bounds 2 4 5 (by decide) (by decide)
    (by decide) (by decide)
  calc
    _ = (2 : ℝ) ^ (1 : ℝ) := by rw [kPellLucas_two]; norm_num [pellLucas]
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

-- Lemma 7 with x = exp 1 and ℓ = 1, where the logarithmic denominator is one.
example : Real.exp 1 < 2 * (5 : ℝ) * Real.log 5 := by
  have hx := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
  have hTx : Real.exp 1 < 5 := Real.exp_one_lt_three.trans (by norm_num)
  simpa using lt_two_rpow_mul_mul_log_rpow_of_one_lt 1 5 (Real.exp 1)
    (by norm_num) hx (by norm_num) (by simpa using hTx)

-- Test section: with `a = 1 / 2` the constant `-log (1 - a) / a` is `2 log 2`, so Lemma 6 gives
-- `|log (1 + x)| < 2 log 2 · |x|` for `0 < |x| < 1 / 2`.
example (x : ℝ) (hx : |x| < 1 / 2) (hx₀ : x ≠ 0) :
    |Real.log (1 + x)| < 2 * Real.log 2 * |x| := by
  have h := (abs_log_one_add_lt_and_abs_lt_exp_sub_one (1 / 2) x (by norm_num) (by norm_num)
    hx hx₀).1
  have hc : -Real.log (1 - 1 / 2) / (1 / 2) = 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
    ring
  rwa [hc] at h

-- Test section: with `a = 1 / 2`, `e^{-1/2} < 2 / 3` since `e^{1/2} > 3 / 2`, so the constant
-- `a / (1 - e^{-a})` is below `3 / 2` and Lemma 6 gives `|x| < (3 / 2) |eˣ - 1|`.
example (x : ℝ) (hx : |x| < 1 / 2) (hx₀ : x ≠ 0) :
    |x| < 3 / 2 * |Real.exp x - 1| := by
  have h := (abs_log_one_add_lt_and_abs_lt_exp_sub_one (1 / 2) x (by norm_num) (by norm_num)
    hx hx₀).2
  have he : Real.exp (-(1 / 2)) < 2 / 3 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.add_one_lt_exp (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  have hk : 1 / 2 / (1 - Real.exp (-(1 / 2))) < 3 / 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  exact h.trans_le (mul_le_mul_of_nonneg_right hk.le (abs_nonneg _))

-- Test section: a negative `x`. At `x = -1 / 4` and `a = 1 / 2` the first bound reads
-- `|log (3 / 4)| < log 2 / 2`, that is `log (4 / 3) < log 2 / 2`, or `(4 / 3) ^ 2 < 2`.
example : |Real.log (3 / 4)| < Real.log 2 / 2 := by
  have h := (abs_log_one_add_lt_and_abs_lt_exp_sub_one (1 / 2) (-(1 / 4)) (by norm_num)
    (by norm_num) (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num) (by norm_num)).1
  have hc : -Real.log (1 - 1 / 2) / (1 / 2) * |(-(1 / 4) : ℝ)| = Real.log 2 / 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    ring
  rwa [hc, show (1 : ℝ) + -(1 / 4) = 3 / 4 by norm_num] at h

-- Test section: the hypothesis `x ≠ 0` is needed. At `x = 0` both sides of each bound vanish, so
-- neither strict inequality holds, whatever `a` is.
example (a : ℝ) :
    ¬ |Real.log (1 + 0)| < -Real.log (1 - a) / a * |(0 : ℝ)| ∧
      ¬ |(0 : ℝ)| < a / (1 - Real.exp (-a)) * |Real.exp 0 - 1| := by
  simp

-- The expansion of `1 / √17 - 1` starts `[-1; 4, …]`. With `M = 3` and `N = 1`, the
-- maximum partial quotient up to `N` is `4`, so the continued-fraction bound gives
-- `1 / 24 < |1 / √17 - 1 + 2 / 2|`.
open GenContFract in
example : 1 / 24 < |(Real.sqrt 17)⁻¹ - 1 - (-2 : ℝ) / 2| := by
  let x := (Real.sqrt 17)⁻¹ - 1
  have hirr : Irrational (Real.sqrt 17) := by
    simpa using (show Nat.Prime 17 by decide).irrational_sqrt
  have hx : Irrational x := by simpa [x] using hirr.inv.sub_intCast 1
  have hs : 4 < Real.sqrt 17 ∧ Real.sqrt 17 < 5 := by
    constructor <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]
  have hinv : 0 < (Real.sqrt 17)⁻¹ := by positivity
  have hlt : (Real.sqrt 17)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [hs.1])
  have hfloor : ⌊x⌋ = -1 := Int.floor_eq_iff.mpr (by
    dsimp [x]
    norm_num
    grind)
  have hfract : Int.fract x = (Real.sqrt 17)⁻¹ := by simp [Int.fract, hfloor, x]
  have hdigit : (GenContFract.of x).s.get? 0 = some ⟨1, 4⟩ := by
    have ht : ⌊Real.sqrt 17⌋ = 4 :=
      Int.floor_eq_iff.mpr (by norm_num; exact ⟨hs.1.le, hs.2⟩)
    change (GenContFract.of x).s.head = _
    simpa [hfract, ht] using of_s_head (v := x) (hfract ▸ hinv.ne')
  have hden := first_den_eq hdigit
  have hpart0 : (GenContFract.of x).partDens.get? 0 = some 4 :=
    partDen_eq_s_b hdigit
  have hinf (i : ℕ) : ¬(GenContFract.of x).TerminatedAt i := by
    intro hi
    obtain ⟨r, hr⟩ := GenContFract.exists_rat_eq_of_terminates ⟨i, hi⟩
    exact hx ⟨r, hr.symm⟩
  have hsome : ∀ j, ∃ b : ℝ, (GenContFract.of x).partDens.get? j = some b := by
    intro j
    exact Option.ne_none_iff_exists'.mp
      (mt GenContFract.terminatedAt_iff_partDen_none.mpr (hinf j))
  let a : ℕ → ℝ := fun n =>
    if n = 0 then ((GenContFract.of x).h : ℝ)
    else ((GenContFract.of x).partDens.get? (n - 1)).getD 0
  have ha0 : a 0 = (GenContFract.of x).h := by simp [a]
  have ha : ∀ j, (GenContFract.of x).partDens.get? j = some (a (j + 1)) := by
    intro j
    obtain ⟨b, hb⟩ := hsome j
    have hbv : a (j + 1) = b := by simp [a, hb]
    rw [hbv, hb]
  have hsup : (Finset.range (1 + 1)).sup' Finset.nonempty_range_add_one a = 4 := by
    have ha0v : a 0 = -1 := by
      rw [ha0]
      simp [GenContFract.of_h_eq_floor, hfloor]
    have ha1v : a 1 = 4 := by
      have hv : a 1 = ((GenContFract.of x).partDens.get? 0).getD 0 := by simp [a]
      rw [hv, hpart0]
      simp
    apply le_antisymm
    · apply Finset.sup'_le Finset.nonempty_range_add_one
      intro i hi
      rw [Finset.mem_range] at hi
      have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with rfl | rfl
      · rw [ha0v]; norm_num
      · rw [ha1v]
    · have hmem : (1 : ℕ) ∈ Finset.range (1 + 1) := Finset.mem_range.mpr (by norm_num)
      rw [← ha1v]
      exact Finset.le_sup' a hmem
  have h := lt_abs_sub_div_of_max_partialQuotient x hx (3 : ℝ) (by norm_num) 1 (by norm_num)
    (by norm_num [hden]) (by intro j hj0 hj1; omega) a ha0 ha 2 (-2) (by norm_num)
    (by norm_num)
  rw [hsup] at h
  norm_num [x] at h ⊢
  exact h

end MathlibExtTest.KPellLucasCloseToPowerOfTwo
