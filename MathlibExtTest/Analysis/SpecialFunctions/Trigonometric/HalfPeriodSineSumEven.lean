/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Trigonometric.HalfPeriodSineSumEven

/-! # Tests for `MathlibExt.Analysis.SpecialFunctions.Trigonometric.HalfPeriodSineSumEven` -/

namespace MathlibExtTest.HalfPeriodSineSumEven

open Real MetaMathlibExt

-- Test section: odd `q`. The sum is `cot (q π / N)`.
example {N q : ℕ} (hN : 0 < N) (hNe : Even N) (hq : Odd q) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * 2 * π / N) = cot (q * π / N) := by
  rw [sum_sin_two_pi_mul_div_of_even hN hNe, ite_eq_right (Nat.not_even_iff_odd.2 hq)]

-- For `N = 4` and `q = 1` the sum is `sin (π / 2) + sin π = 1`, which evaluates `cot (π / 4)`.
example : cot (π / 4) = 1 := by
  have h := sum_sin_two_pi_mul_div_of_even (N := 4) (by norm_num) (by decide) 1
  rw [ite_eq_right (by decide), show (4 : ℕ) / 2 = 2 from rfl,
    Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton] at h
  rw [show π / 4 = ((1 : ℕ) : ℝ) * π / ((4 : ℕ) : ℝ) by push_cast; ring, ← h]
  push_cast
  rw [show (1 : ℝ) * 1 * 2 * π / 4 = π / 2 by ring, show (1 : ℝ) * 2 * 2 * π / 4 = π by ring,
    sin_pi_div_two, sin_pi, add_zero]

-- For `N = 6` and `q = 1` the sum is `sin (π / 3) + sin (2π / 3) + sin π = √3`, which evaluates
-- `cot (π / 6)`.
example : cot (π / 6) = √3 := by
  have h := sum_sin_two_pi_mul_div_of_even (N := 6) (by norm_num) (by decide) 1
  rw [ite_eq_right (by decide), show (6 : ℕ) / 2 = 3 from rfl,
    Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
    Finset.Icc_self, Finset.sum_singleton] at h
  rw [show π / 6 = ((1 : ℕ) : ℝ) * π / ((6 : ℕ) : ℝ) by push_cast; ring, ← h]
  push_cast
  rw [show (1 : ℝ) * 1 * 2 * π / 6 = π / 3 by ring,
    show (1 : ℝ) * 2 * 2 * π / 6 = π - π / 3 by ring, show (1 : ℝ) * 3 * 2 * π / 6 = π by ring,
    sin_pi_sub, sin_pi_div_three, sin_pi]
  ring

-- Test section: even `q`. The sum is `0`.
example {N q : ℕ} (hN : 0 < N) (hNe : Even N) (hq : Even q) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * 2 * π / N) = 0 := by
  rw [sum_sin_two_pi_mul_div_of_even hN hNe, ite_eq_left hq]

-- `q = 0`, which the paper excludes, is covered.
example {N : ℕ} (hN : 0 < N) (hNe : Even N) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (((0 : ℕ) : ℝ) * l * 2 * π / N) = 0 :=
  (sum_sin_two_pi_mul_div_of_even hN hNe 0).trans (ite_eq_left Even.zero)

-- Test section: hypotheses. `Even N` cannot be dropped: for `N = 3` and `q = 2` the sum is
-- `sin (4π / 3) = -sin (π / 3) ≠ 0`.
example : ¬ ∀ {N : ℕ}, 0 < N → ∀ q : ℕ,
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * 2 * π / N) =
      if Even q then 0 else cot (q * π / N) := by
  intro h
  have h3 := h (N := 3) (by norm_num) 2
  rw [ite_eq_left (by decide), show (3 : ℕ) / 2 = 1 from rfl, Finset.Icc_self,
    Finset.sum_singleton] at h3
  push_cast at h3
  rw [show (2 : ℝ) * 1 * 2 * π / 3 = π / 3 + π by ring, sin_add_pi, neg_eq_zero] at h3
  exact (sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])).ne' h3

-- The source's `0 < N` is kept, but the conclusion also holds at `N = 0`: the sum is empty, and
-- the junk values `x / 0 = 0` and `cot 0 = 0` make the right-hand side `0`.
example (q : ℕ) :
    ∑ l ∈ Finset.Icc 1 ((0 : ℕ) / 2), sin (q * l * 2 * π / (0 : ℕ)) =
      if Even q then 0 else cot (q * π / (0 : ℕ)) := by
  simp [cot_eq_cos_div_sin]

-- Test section: odd modulus, `sum_sin_two_pi_mul_div_of_odd`. For even `q` the sum is
-- `-(1/2) tan (q π / (2 N))`.
example {N q : ℕ} (hN : Odd N) (hq : Even q) :
    ∑ l ∈ Finset.Icc 1 ((N - 1) / 2), sin (q * l * 2 * π / N) =
      -(1 / 2) * tan (q * π / (2 * N)) := by
  rw [sum_sin_two_pi_mul_div_of_odd hN, ite_eq_left hq]

-- For odd `q` it is `(1/2) cot (q π / (2 N))`.
example {N q : ℕ} (hN : Odd N) (hq : Odd q) :
    ∑ l ∈ Finset.Icc 1 ((N - 1) / 2), sin (q * l * 2 * π / N) =
      1 / 2 * cot (q * π / (2 * N)) := by
  rw [sum_sin_two_pi_mul_div_of_odd hN, ite_eq_right (Nat.not_even_iff_odd.2 hq)]

-- For `N = 3` and `q = 1` the sum is `sin (2π / 3) = √3 / 2`, which evaluates `cot (π / 6)`.
example : cot (π / 6) = √3 := by
  have h := sum_sin_two_pi_mul_div_of_odd (N := 3) (by decide) 1
  rw [ite_eq_right (by decide), show (3 - 1) / 2 = 1 from rfl, Finset.Icc_self,
    Finset.sum_singleton] at h
  push_cast at h
  rw [show (1 : ℝ) * 1 * 2 * π / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three,
    show (1 : ℝ) * π / (2 * 3) = π / 6 by ring] at h
  linarith

-- For `N = 3` and `q = 2` the sum is `sin (4π / 3) = -√3 / 2`, which evaluates `tan (π / 3)`.
example : tan (π / 3) = √3 := by
  have h := sum_sin_two_pi_mul_div_of_odd (N := 3) (by decide) 2
  rw [ite_eq_left (by decide), show (3 - 1) / 2 = 1 from rfl, Finset.Icc_self,
    Finset.sum_singleton] at h
  push_cast at h
  rw [show (2 : ℝ) * 1 * 2 * π / 3 = π / 3 + π by ring, sin_add_pi, sin_pi_div_three,
    show (2 : ℝ) * π / (2 * 3) = π / 3 by ring] at h
  linarith

-- For `N = 1` the sum is empty, so for `q = 1` the theorem gives `cot (π / 2) = 0`.
example : cot (π / 2) = 0 := by
  have h := sum_sin_two_pi_mul_div_of_odd (N := 1) (by decide) 1
  rw [ite_eq_right (by decide), show (1 - 1) / 2 = 0 from rfl, Finset.Icc_eq_empty (by norm_num),
    Finset.sum_empty] at h
  push_cast at h
  rw [show (1 : ℝ) * π / (2 * 1) = π / 2 by ring] at h
  linarith

-- For `N = 3` and `q = 6`, `N` divides `q`: the sum is `sin (4π) = 0`, and so is `tan π`.
example : ∑ l ∈ Finset.Icc 1 ((3 - 1) / 2 : ℕ), sin (((6 : ℕ) : ℝ) * l * 2 * π / (3 : ℕ)) = 0 := by
  rw [sum_sin_two_pi_mul_div_of_odd (by decide), ite_eq_left (by decide)]
  push_cast
  rw [show (6 : ℝ) * π / (2 * 3) = π by ring, tan_pi, mul_zero]

-- `q = 0`, which the paper excludes, is covered.
example {N : ℕ} (hN : Odd N) :
    ∑ l ∈ Finset.Icc 1 ((N - 1) / 2), sin (((0 : ℕ) : ℝ) * l * 2 * π / N) = 0 := by
  rw [sum_sin_two_pi_mul_div_of_odd hN, ite_eq_left Even.zero]
  simp

-- Test section: even modulus and even multiplier, `sum_sin_pi_mul_div_of_even_of_even`. For
-- `q ≡ 2 (mod 4)` the sum is `cot (q π / (2 N))`.
example {N q : ℕ} (hN : 0 < N) (hNe : Even N) (hq : q % 4 = 2) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * π / N) = cot (q * π / (2 * N)) := by
  rw [sum_sin_pi_mul_div_of_even_of_even hN hNe (Nat.even_iff.2 (by omega)),
    ite_eq_right (by omega)]

-- For `q ≡ 0 (mod 4)` it is `0`.
example {N q : ℕ} (hN : 0 < N) (hNe : Even N) (hq : q % 4 = 0) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * π / N) = 0 := by
  rw [sum_sin_pi_mul_div_of_even_of_even hN hNe (Nat.even_iff.2 (by omega)), ite_eq_left hq]

-- For `N = 4` and `q = 2` the sum is `sin (π / 2) + sin π = 1`, which evaluates `cot (π / 4)`.
example : cot (π / 4) = 1 := by
  have h := sum_sin_pi_mul_div_of_even_of_even (N := 4) (q := 2) (by norm_num) (by decide)
    (by decide)
  rw [ite_eq_right (by decide), show (4 : ℕ) / 2 = 2 from rfl,
    Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton] at h
  push_cast at h
  rw [show (2 : ℝ) * 1 * π / 4 = π / 2 by ring, show (2 : ℝ) * 2 * π / 4 = π by ring,
    sin_pi_div_two, sin_pi, add_zero, show (2 : ℝ) * π / (2 * 4) = π / 4 by ring] at h
  exact h.symm

-- For `N = 4` and `q = 4` the sum `sin π + sin (2π)` is `0`.
example : ∑ l ∈ Finset.Icc 1 ((4 : ℕ) / 2), sin (((4 : ℕ) : ℝ) * l * π / (4 : ℕ)) = 0 := by
  rw [sum_sin_pi_mul_div_of_even_of_even (by norm_num) (by decide) (by decide),
    ite_eq_left (by decide)]

-- For `N = 2` and `q = 2`, `N` divides `q`: the sum is `sin π = 0`, and so is `cot (π / 2)`.
example : ∑ l ∈ Finset.Icc 1 ((2 : ℕ) / 2), sin (((2 : ℕ) : ℝ) * l * π / (2 : ℕ)) = 0 := by
  rw [sum_sin_pi_mul_div_of_even_of_even (by norm_num) (by decide) (by decide),
    ite_eq_right (by decide)]
  push_cast
  rw [show (2 : ℝ) * π / (2 * 2) = π / 2 by ring, cot_eq_cos_div_sin, cos_pi_div_two, zero_div]

-- `q = 0`, which the paper excludes, is covered.
example {N : ℕ} (hN : 0 < N) (hNe : Even N) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (((0 : ℕ) : ℝ) * l * π / N) = 0 := by
  rw [sum_sin_pi_mul_div_of_even_of_even hN hNe Even.zero, ite_eq_left (by decide)]

end MathlibExtTest.HalfPeriodSineSumEven
