/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GoldenRatioLogCounts

/-! # Tests for the golden-ratio logarithm counts -/

open MetaMathlibExt Real
open scoped goldenRatio

-- Compute the sequence directly, including the initial values and both signs in the recurrence.
example : alternatingSignFibonacci 0 = 0 ∧ alternatingSignFibonacci 1 = 1 ∧
    alternatingSignFibonacci 2 = 2 ∧ alternatingSignFibonacci 3 = 2 ∧
    alternatingSignFibonacci 4 = 5 := by decide

-- Check an interval by comparing the logarithms at its first and last points and their neighbors.
private theorem bucket_of_power_bounds {m a b : ℕ} (ha : 1 < a) (hab : a < b)
    (hlo : ((a - 1 : ℕ) : ℝ) < φ ^ m) (haφ : φ ^ m ≤ (a : ℝ))
    (hhi : ((b - 1 : ℕ) : ℝ) < φ ^ (m + 1)) (hbφ : φ ^ (m + 1) ≤ (b : ℝ)) :
    {n : ℕ | 1 ≤ n ∧ ⌊logb φ n⌋₊ = m} = (Finset.Ico a b : Set ℕ) := by
  have h₀ : logb φ ((a - 1 : ℕ) : ℝ) < m := by
    have ha₀ : (0 : ℝ) < ((a - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < a - 1 by omega)
    rwa [logb_lt_iff_lt_rpow one_lt_goldenRatio ha₀, rpow_natCast]
  have h₁ : (m : ℝ) ≤ logb φ a := by
    have ha₀ : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    rwa [le_logb_iff_rpow_le one_lt_goldenRatio ha₀, rpow_natCast]
  have h₂ : logb φ ((b - 1 : ℕ) : ℝ) < (m : ℝ) + 1 := by
    have hb₀ : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < b - 1 by omega)
    rwa [← Nat.cast_succ, logb_lt_iff_lt_rpow one_lt_goldenRatio hb₀, rpow_natCast]
  have h₃ : (m : ℝ) + 1 ≤ logb φ b := by
    have hb₀ : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    rwa [← Nat.cast_succ, le_logb_iff_rpow_le one_lt_goldenRatio hb₀, rpow_natCast]
  have hmono {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : logb φ i ≤ logb φ j := by
    have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hip := zero_lt_one.trans_le hi'
    exact (strictMonoOn_logb one_lt_goldenRatio).monotoneOn hip (hip.trans_le hij') hij'
  ext n
  rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Ico]
  have hfloor (hn : 1 ≤ n) := Nat.floor_eq_iff (n := m)
    (logb_nonneg one_lt_goldenRatio (show (1 : ℝ) ≤ n by exact_mod_cast hn))
  constructor
  · rintro ⟨hn, he⟩
    obtain ⟨hl, hu⟩ := (hfloor hn).mp he
    constructor
    · by_contra! han
      exact (not_lt_of_ge hl) ((hmono hn (by omega : n ≤ a - 1)).trans_lt h₀)
    · by_contra! hnb
      exact (not_lt_of_ge (h₃.trans (hmono (by omega) hnb))) hu
  · rintro ⟨han, hnb⟩
    have hn : 1 ≤ n := by omega
    exact ⟨hn, (hfloor hn).mpr
      ⟨h₁.trans (hmono (by omega) han), (hmono hn (by omega : n ≤ b - 1)).trans_lt h₂⟩⟩

-- The first positive bucket is exactly {2}; this uses no Lucas identity or count theorem.
private theorem first_bucket :
    {n : ℕ | 1 ≤ n ∧ ⌊logb φ n⌋₊ = 1} = (Finset.Ico 2 3 : Set ℕ) := by
  apply bucket_of_power_bounds (by decide) (by decide) <;>
    norm_num [goldenRatio_sq] <;> linarith only [one_lt_goldenRatio, goldenRatio_lt_two]

-- The next bucket is exactly {3, 4}, checked from the second and third powers of φ.
private theorem second_bucket :
    {n : ℕ | 1 ≤ n ∧ ⌊logb φ n⌋₊ = 2} = (Finset.Ico 3 5 : Set ℕ) := by
  have hφ : (3 / 2 : ℝ) < φ := by
    rw [goldenRatio]
    have hsqrt : (2 : ℝ) < √5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith
  have hcube : φ ^ (3 : ℕ) = 2 * φ + 1 := by
    rw [pow_succ, goldenRatio_sq, add_mul, ← pow_two, goldenRatio_sq, one_mul]
    ring
  apply bucket_of_power_bounds (by decide) (by decide) <;>
    norm_num [goldenRatio_sq, hcube] <;> linarith only [hφ, goldenRatio_lt_two]

-- Count both certified sets and compare with the sequence by computation, not by the theorem.
example :
    ({n : ℕ | 1 ≤ n ∧ ⌊logb φ n⌋₊ = 1}.ncard : ℤ) = alternatingSignFibonacci 1 ∧
      ({n : ℕ | 1 ≤ n ∧ ⌊logb φ n⌋₊ = 2}.ncard : ℤ) = alternatingSignFibonacci 2 := by
  rw [first_bucket, second_bucket, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Nat.card_Ico, Nat.card_Ico]
  decide

-- A client can get the fourth count from the public theorem and the computed sequence value.
example : ({n : ℕ | 1 ≤ n ∧ ⌊logb φ n⌋₊ = 4}.ncard : ℤ) = 5 :=
  (ncard_floor_logb_goldenRatio_eq_alternatingSignFibonacci 4 (by decide)).trans (by decide)
