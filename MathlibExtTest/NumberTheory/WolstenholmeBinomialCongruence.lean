/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WolstenholmeBinomialCongruence

/-! # Tests for the general and fourth-power binomial congruences -/

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

private def powFourRemainder (n : ℤ) (k : ℕ) : ℚ :=
  let C (x : ℤ) (r : ℕ) : ℚ := (Ring.choose x r : ℤ)
  let N : ℚ := n
  C (n * 7) (k * 7) - C n k -
    (k : ℚ) * (N - k) / 2 * C n k *
      ((N - 4) + (3 - N) * ((14 : ℕ).choose 7 : ℚ) + (N - 2) / 3 * ((21 : ℕ).choose 7 : ℚ))

-- At the least admissible prime, n = 3 forces exact equality even when k = 2.
example : Ring.choose (3 : ℤ) 4 = 0 ∧ powFourRemainder 3 2 = 0 := by
  have h21 : Ring.choose (21 : ℤ) 14 = 116280 := by
    change Ring.choose ((21 : ℕ) : ℤ) 14 = 116280
    rw [Ring.choose_natCast, Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  norm_num [powFourRemainder, h21, show Ring.choose (3 : ℤ) 4 = 0 by decide,
    show Ring.choose (3 : ℤ) 2 = 3 by decide, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

-- With k = 0 the correction vanishes, also for negative n.
example : powFourRemainder (-4) 0 = 0 := by
  simp [powFourRemainder]

private lemma powFourRemainder_neg_four : powFourRemainder (-4) 1 = (7 : ℚ) ^ 7 * (-4) := by
  dsimp only [powFourRemainder]
  change ((Ring.choose (-28 : ℤ) 7 : ℤ) : ℚ) - _ - _ = _
  rw [Ring.choose_neg, Ring.choose_one_right]
  change ((Int.negOnePow 7 • Ring.choose ((34 : ℕ) : ℤ) 7 : ℤ) : ℚ) - _ - _ = _
  simp only [Ring.choose_natCast, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

-- For a negative upper index the error is nonzero, and choose(-4, 4) adds one to the bound.
example : powFourRemainder (-4) 1 ≠ 0 ∧
    padicValRat 7 ((Ring.choose (-4 : ℤ) 4 : ℤ) : ℚ) = 1 ∧
    padicValRat 7 (powFourRemainder (-4) 1) = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hunit (z : ℤ) (hz : ¬ (7 : ℤ) ∣ z) : padicValRat 7 (z : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz, Nat.cast_zero]
  have h7 : padicValRat 7 (7 : ℚ) = 1 := padicValRat.self (by decide)
  have h5 : padicValRat 7 (5 : ℚ) = 0 := hunit 5 (by decide)
  have hneg4 : padicValRat 7 (-4 : ℚ) = 0 := hunit (-4) (by decide)
  rw [powFourRemainder_neg_four, show Ring.choose (-4 : ℤ) 4 = 35 by decide, Int.cast_ofNat,
    show (35 : ℚ) = 7 * 5 by norm_num,
    padicValRat.mul (by norm_num : (7 : ℚ) ≠ 0) (by norm_num : (5 : ℚ) ≠ 0),
    padicValRat.mul (by norm_num : (7 : ℚ) ^ 7 ≠ 0) (by norm_num : (-4 : ℚ) ≠ 0),
    padicValRat.pow, h7, h5, hneg4]
  norm_num

-- Check that a client can use the new theorem at the same nontrivial input.
example : 4 + padicValRat 7 ((Ring.choose (-4 : ℤ) 4 : ℤ) : ℚ) ≤
    padicValRat 7 (powFourRemainder (-4) 1) := by
  have h := ringChoose_mul_prime_sub_congr_pow_four 7 1 (-4) (by decide) (by decide)
  change powFourRemainder (-4) 1 = 0 ∨ _ at h
  exact (h.resolve_left (by rw [powFourRemainder_neg_four]; norm_num)).2
