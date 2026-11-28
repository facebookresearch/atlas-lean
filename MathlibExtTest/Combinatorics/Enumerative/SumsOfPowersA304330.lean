/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

-- Even the last binomial coefficient vanishes when k exceeds twice the upper endpoint.
example (k n : ℕ) (hn : 1 ≤ n) (hk : 2 * n < k) :
    (∑ i ∈ Finset.Icc 1 n, (2 * i) * (2 * i + k - 1).choose (2 * k - 1)) = 0 := by
  rw [sum_two_mul_choose_eq k n (by omega) hn,
    Nat.choose_eq_zero_of_lt (show 2 * n + k + 1 < 2 * k + 1 by omega), mul_zero]

-- At k = 2n, the final summand is the first nonzero one.
example (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n, (2 * i) * (2 * i + 2 * n - 1).choose (2 * (2 * n) - 1)) =
      2 * n := by
  rw [sum_two_mul_choose_eq (2 * n) n (by omega) hn, ← two_mul (2 * n), Nat.choose_self, mul_one]

-- Every term vanishes below the first nonzero binomial coefficient.
example (k n : ℕ) (hn : 1 ≤ n) (hnk : n < k) :
    (∑ i ∈ Finset.Icc 1 n, (i : ℚ) * (i + k - 1).choose (2 * k - 1)) = 0 := by
  rw [sum_mul_choose_eq k n (by omega) hn, Nat.choose_eq_zero_of_lt (show n + k < 2 * k by omega)]
  simp

-- At k = 2 and n = 3, the prefactor is 14/5 and the binomial coefficient is 5.
example : (∑ i ∈ Finset.Icc 1 (3 : ℕ), (i : ℚ) * (i + 2 - 1).choose 3) = 14 := by
  rw [sum_mul_choose_eq 2 3 (by decide) (by decide)]
  norm_num [Nat.choose]

-- The first row covered by the theorem has two nonzero entries.
example : arrayR 2 1 = 1 ∧ arrayR 2 2 = 12 ∧ arrayR 2 3 = 0 := by decide

-- At k = 1 the only summand survives, so the lower bound is sharp.
example : (∑ m ∈ Finset.Icc 1 (1 : ℕ),
    (-1 : ℚ) ^ m * ((Nat.factorial (m - 1) : ℚ) ^ 2 / ((2 * m).factorial : ℚ)) *
      (arrayR 1 m : ℚ)) = -1 / 2 := by
  norm_num [show arrayR 1 1 = 1 by decide, Nat.factorial]

-- At m = 1 the only admissible tuple is (0, 0, 1), so the closed form gives R(3, 1) = 1.
example : (arrayR 3 1 : ℚ) = 1 := by
  rw [arrayR_eq_closedForm 3 1 le_rfl (by norm_num),
    show (Finset.univ.filter fun b : Fin 3 → Fin 4 =>
      (∑ r : Fin 3, (r.val + 1) * (b r).val) = 3 ∧ (∑ r : Fin 3, (b r).val) = 1) =
      {![0, 0, 1]} by decide]
  norm_num [Fin.prod_univ_three, Nat.factorial]

-- At m = k the only admissible tuple is (3, 0, 0), so the closed form gives R(3, 3) = 6! / 2.
example : (arrayR 3 3 : ℚ) = 360 := by
  rw [arrayR_eq_closedForm 3 3 (by norm_num) le_rfl,
    show (Finset.univ.filter fun b : Fin 3 → Fin 4 =>
      (∑ r : Fin 3, (r.val + 1) * (b r).val) = 3 ∧ (∑ r : Fin 3, (b r).val) = 3) =
      {![3, 0, 0]} by decide]
  norm_num [Fin.prod_univ_three, Nat.factorial]

-- At k = 4 and m = 2 two tuples are admissible, (1, 0, 1, 0) and (0, 2, 0, 0), and their
-- terms add up to R(4, 2) = 252.
example : (arrayR 4 2 : ℚ) = 252 := by
  rw [arrayR_eq_closedForm 4 2 (by norm_num) (by norm_num),
    show (Finset.univ.filter fun b : Fin 4 → Fin 5 =>
      (∑ r : Fin 4, (r.val + 1) * (b r).val) = 4 ∧ (∑ r : Fin 4, (b r).val) = 2) =
      {![1, 0, 1, 0], ![0, 2, 0, 0]} by decide +kernel]
  norm_num [Fin.prod_univ_four, Nat.factorial]

-- The first positive row vanishes just above the diagonal.
example : arrayU 1 2 = 0 := by
  norm_num [arrayU, Finset.sum_range_succ, Nat.choose, Nat.factorial]

-- Recover the third term, where the middle coefficient of the inverse is five.
example (a b : ℕ → ℝ) (h : ∀ k : ℕ, 1 ≤ k → a k =
    ∑ m ∈ Finset.Icc 1 k, (MetaMathlibExt.jacobiStirlingFirst k m (0 : ℤ) : ℝ) * b m) :
    b 3 = a 1 + 5 * a 2 + a 3 := by
  have h₃ := (inversion_uU a b).mp h 3 (by decide)
  rw [show Finset.Icc 1 (3 : ℕ) = {1, 2, 3} by decide] at h₃
  norm_num [arrayU, Finset.sum_range_succ, Nat.choose, Nat.factorial] at h₃
  simpa [add_assoc] using h₃

-- The inverse allows an arbitrary zeroth term, as both sums start at one.
example (a : ℕ → ℝ) (b₀ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    a k = ∑ m ∈ Finset.Icc 1 k, (MetaMathlibExt.jacobiStirlingFirst k m (0 : ℤ) : ℝ) *
      (if m = 0 then b₀ else ∑ i ∈ Finset.Icc 1 m, (arrayU m i : ℝ) * a i) := by
  let b (m : ℕ) := if m = 0 then b₀ else ∑ i ∈ Finset.Icc 1 m, (arrayU m i : ℝ) * a i
  apply (inversion_uU a b).mpr _ k hk
  intro m hm
  simp [b, show m ≠ 0 by omega]

-- At the empty endpoint the first binomial coefficient is one, but its coefficient vanishes.
example (k : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ Finset.Icc 1 k, thmQ k m 0 * (m.choose (2 * m - 1) : ℚ)) = 0 := by
  simpa [powerSum] using (pow_mul_powerSum_odd_eq_sum k hk 0).symm

-- The middle column of the fifth-power formula receives contributions from two entries of R.
example (n : ℕ) : 32 * powerSum 5 n =
    (n : ℚ) ^ 5 * (n + 1) + (20 * (n : ℚ) ^ 3 + 10 * n) * (n + 2).choose 3 +
      120 * (n : ℚ) * (n + 3).choose 5 := by
  have h := pow_mul_powerSum_odd_eq_sum 3 (by decide) n
  rw [show Finset.Icc 1 (3 : ℕ) = {1, 2, 3} by decide] at h
  norm_num [thmQ, show Finset.Icc 2 (3 : ℕ) = {2, 3} by decide,
    show arrayR 1 1 = 1 by decide, show arrayR 2 1 = 1 by decide,
    show arrayR 2 2 = 12 by decide, show Nat.choose 5 2 = 10 by decide] at h
  rw [h]
  ring

-- At the empty endpoint, every positive column has a vanishing binomial coefficient.
example (k : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ Finset.Icc 1 k, (arrayR k m : ℚ) * (m + 1).choose (2 * m + 1)) = 0 := by
  simpa [powerSum] using (pow_mul_powerSum_even_eq_sum k hk 0).symm

-- The fourth-power formula has coefficients 1 and 12 for every upper endpoint.
example (n : ℕ) : 16 * powerSum 4 n =
    ((2 * n + 2).choose 3 : ℚ) + 12 * (2 * n + 3).choose 5 := by
  have h := pow_mul_powerSum_even_eq_sum 2 (by decide) n
  rw [show Finset.Icc 1 (2 : ℕ) = {1, 2} by decide] at h
  norm_num [show arrayR 2 1 = 1 by decide, show arrayR 2 2 = 12 by decide, Nat.add_assoc] at h
  exact h

-- In the forward direction, the two columns for k = 2 have different scaling factors.
example (a : ℕ → ℝ) (h : ∀ n : ℕ, (powerSum 4 n : ℝ) / (2 * (n : ℝ) + 1) =
    ∑ m ∈ Finset.Icc 1 (2 : ℕ), a m * ((n + m).choose (2 * m) : ℝ)) :
    (powerSum 3 3 : ℝ) = 18 * a 1 + (25 / 2) * a 2 := by
  have h₃ := (powerSum_even_div_iff_odd 2 (by decide) a).mp h 3
  rw [show Finset.Icc 1 (2 : ℕ) = {1, 2} by decide] at h₃
  norm_num [Nat.choose] at h₃
  rw [h₃]
  ring

-- In the reverse direction at k = 1, the same coefficient works at zero and at n = 2.
example (a : ℕ → ℝ) (h : ∀ n : ℕ, (powerSum 1 n : ℝ) =
    3 * a 1 * ((n + 1).choose 2 : ℝ)) :
    (powerSum 2 0 : ℝ) = 0 ∧ (powerSum 2 2 : ℝ) / 5 = 3 * a 1 := by
  have he := (powerSum_even_div_iff_odd 1 le_rfl a).mpr (fun n ↦ by
    norm_num
    exact h n)
  constructor
  · have h₀ := he 0
    norm_num [Nat.choose] at h₀
    exact_mod_cast h₀
  · have h₂ := he 2
    norm_num [Nat.choose] at h₂
    simpa [mul_comm (a 1)] using h₂

-- The upper binomial column vanishes when the endpoint is smaller than its index.
example : powerSum 4 1 = 1 := by
  rw [powerSum_even_eq_sum 2 (by decide)]
  rw [show Finset.Icc 1 (2 : ℕ) = {1, 2} by decide]
  norm_num [Nat.choose, show arrayR 2 1 = 1 by decide]

-- Both columns contribute to the sum of the first three fourth powers.
example : powerSum 4 3 = 98 := by
  rw [powerSum_even_eq_sum 2 (by decide)]
  rw [show Finset.Icc 1 (2 : ℕ) = {1, 2} by decide]
  norm_num [Nat.choose, show arrayR 2 1 = 1 by decide, show arrayR 2 2 = 12 by decide]

-- At n = 0 the expansion has no nonzero summands, for any positive k.
example (k : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ Finset.Icc 1 k, (arrayR k m : ℚ) * (1 / (2 * (m : ℚ) + 1)) *
      (m.choose (2 * m) : ℚ)) = 0 := by
  simpa [powerSum] using (powerSum_even_eq_sum k hk 0).symm

-- The factor S₂ vanishes at the empty endpoint for every positive k.
example (k : ℕ) (hk : 1 ≤ k) : powerSum (2 * k) 0 = 0 := by
  rw [powerSum_even_faulhaber (k := k) (hk := hk) (n := 0)]
  simp [powerSum]

-- The quartic Faulhaber form has coefficients −1/5 and 6/5.
example (n : ℕ) : powerSum 4 n = powerSum 2 n * (-1 / 5 + (6 / 5) * powerSum 1 n) := by
  have h11 := MetaMathlibExt.legendreStirlingFirst_diag 1
  have h22 := MetaMathlibExt.legendreStirlingFirst_diag 2
  have h10 : MetaMathlibExt.legendreStirlingFirst 1 0 = 0 := by
    simp [MetaMathlibExt.legendreStirlingFirst, MetaMathlibExt.jacobiStirlingFirst,
      MetaMathlibExt.jacobiStirlingFirstPoly]
  have h21 : MetaMathlibExt.legendreStirlingFirst 2 1 = -2 := by
    rw [MetaMathlibExt.legendreStirlingFirst_succ 1 0]
    norm_num [h10, h11]
  have h := powerSum_even_faulhaber (k := 2) (hk := by decide) (n := n)
  rw [show Finset.Icc 1 (2 : ℕ) = {1, 2} by decide] at h
  norm_num [faulhaberB, show Finset.Icc 1 (2 : ℕ) = {1, 2} by decide, h11, h21, h22,
    show arrayR 2 1 = 1 by decide, show arrayR 2 2 = 12 by decide, Nat.factorial] at h
  rw [h]
  ring

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
