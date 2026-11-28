/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CompletelyAdditiveHeightSumHeightAsymptotic

/-!
# Tests for prime reduction for summatory heights

Constant prime weights and weights supported at two give nonzero error bounds at an
integer and a noninteger input.
-/

namespace MathlibExtTest.NumberTheory.CompletelyAdditiveHeightSumHeightAsymptotic

open MetaMathlibExt

private lemma sum_four {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    (∑ m ∈ Finset.Icc 1 4, (H m : ℝ)) = 3 * (H 2 : ℝ) + H 3 := by
  have h : ∑ m ∈ Finset.Icc 1 4, H m = 3 * H 2 + H 3 := by
    rw [sum_height_eq_sum_prime_powers hH (by decide),
      show (Finset.Iic 4).filter Nat.Prime = {2, 3} by decide,
      Finset.sum_pair (by decide)]
    rw [show (Finset.Icc 1 4).filter (fun a => 2 ^ a ≤ 4) = {1, 2} by decide,
      show (Finset.Icc 1 4).filter (fun a => 3 ^ a ≤ 4) = {1} by decide,
      Finset.sum_pair (by decide), Finset.sum_singleton]
    simp
    omega
  exact_mod_cast h

example : ∃ C : ℝ, (2 : ℝ) ≤ C * Real.log 4 * 2 ∧
    (11 / 4 : ℝ) ≤ C * Real.log (9 / 2) * 2 := by
  let H := additiveOfPrimeValues (fun _ => 1)
  have hH : IsCompletelyAdditiveNat H := isCompletelyAdditiveNat_additiveOfPrimeValues _
  obtain ⟨C, hC⟩ := sum_height_asymptotic hH
  have h₂ : H 2 = 1 := additiveOfPrimeValues_prime _ Nat.prime_two
  have h₃ : H 3 = 1 := additiveOfPrimeValues_prime _ Nat.prime_three
  have hP : (Finset.Iic 4).filter Nat.Prime = {2, 3} := by decide
  have hf : ⌊(9 / 2 : ℝ)⌋₊ = 4 := by
    rw [Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 9 / 2)]
    norm_num
  have h₄ := hC 4 (by norm_num)
  have hhalf := hC (9 / 2) (by norm_num)
  refine ⟨C, ?_, ?_⟩
  · convert h₄ using 1 <;> norm_num [hP, sum_four hH, h₂, h₃]
  · convert hhalf using 1 <;> norm_num [hf, hP, sum_four hH, h₂, h₃]

example : ∃ C : ℝ, (1 : ℝ) ≤ C * Real.log 4 ∧
    (3 / 2 : ℝ) ≤ C * Real.log (9 / 2) := by
  let H := additiveOfPrimeValues (fun p => if p = 2 then 1 else 0)
  have hH : IsCompletelyAdditiveNat H := isCompletelyAdditiveNat_additiveOfPrimeValues _
  obtain ⟨C, hC⟩ := sum_height_asymptotic hH
  have h₂ : H 2 = 1 := by simp [H, additiveOfPrimeValues_prime _ Nat.prime_two]
  have h₃ : H 3 = 0 := by simp [H, additiveOfPrimeValues_prime _ Nat.prime_three]
  have hP : (Finset.Iic 4).filter Nat.Prime = {2, 3} := by decide
  have hf : ⌊(9 / 2 : ℝ)⌋₊ = 4 := by
    rw [Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 9 / 2)]
    norm_num
  have h₄ := hC 4 (by norm_num)
  have hhalf := hC (9 / 2) (by norm_num)
  refine ⟨C, ?_, ?_⟩
  · convert h₄ using 1 <;> norm_num [hP, sum_four hH, h₂, h₃]
  · convert hhalf using 1 <;> norm_num [hf, hP, sum_four hH, h₂, h₃]

end MathlibExtTest.NumberTheory.CompletelyAdditiveHeightSumHeightAsymptotic
