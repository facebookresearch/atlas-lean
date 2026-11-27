/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WolstenholmeBinomialCongruence

/-! # Tests for the general binomial congruence -/

open MetaMathlibExt

-- For a nonnegative upper index at most m, the corrections give exact equality.
example (p m k n : ℕ) (hp : p.Prime) (hm : m + 1 < p) (hn : n ≤ m) :
    let C (x : ℤ) (i : ℕ) : ℚ := (Ring.choose x i : ℤ)
    let c (j : ℕ) := ∑ s ∈ Finset.range (j + 1), if s ≤ k then
      C (j * p : ℕ) (s * p) * C ((n : ℤ) - j) (k - s) else 0
    C ((n : ℤ) * p) (k * p) - C n k = ∑ l ∈ Finset.Icc 1 m,
      C n l * ∑ j ∈ Finset.range (l + 1), (-1) ^ (l - j) * (l.choose j : ℚ) * c j := by
  intro C c
  have h := ringChoose_mul_prime_sub_congr_sum_d p m k n hp hm
  have hz : C n (m + 1) = 0 := by
    simp only [C, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show n < m + 1 by omega),
      Nat.cast_zero, Int.cast_zero]
  exact sub_eq_zero.mp (h.resolve_right (fun h' => h'.1 hz))

-- At n = -3 the second correction is 1500, and the extra factor from choose(-3, 3) is 5.
example : 3 + padicValRat 5 (-10) ≤ padicValRat 5 (-13125) := by
  have h := ringChoose_mul_prime_sub_congr_sum_d 5 2 1 (-3) (by decide) (by decide)
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  norm_num [hI, Finset.sum_range_succ, Ring.choose_one_right, Ring.choose_zero_right] at h
  norm_num [show Ring.choose (-15 : ℤ) 5 = -11628 by decide,
    show Ring.choose (-3 : ℤ) 2 = 6 by decide, show Ring.choose (-3 : ℤ) 3 = -10 by decide,
    show Ring.choose (5 : ℤ) 5 = 1 by decide, show Ring.choose (10 : ℤ) 5 = 252 by decide] at h
  rw [← padicValRat.of_int] at h
  simpa only [Int.cast_neg, Int.cast_ofNat, padicValRat.neg] using h
