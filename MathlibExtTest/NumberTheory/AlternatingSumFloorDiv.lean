/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingSumFloorDiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.NumberTheory.AlternatingSumFloorDiv` -/

namespace MathlibExtTest.AlternatingSumFloorDiv

open MetaMathlibExt MetaMathlibExt.AlternatingSumFloorDiv

-- Test section: alternating sums of antitone nonnegative sequences.

-- For the constant sequence `1` the partial sums alternate between `1` and `0`, so both ends of
-- the interval `[0, f 0]` are attained.
example : ∑ j ∈ Finset.range 3, (-1 : ℝ) ^ j * 1 = 1 := by norm_num [Finset.sum_range_succ]

example : ∑ j ∈ Finset.range 4, (-1 : ℝ) ^ j * 1 = 0 := by norm_num [Finset.sum_range_succ]

example (L : ℕ) : ∑ j ∈ Finset.range L, (-1 : ℝ) ^ j * 1 ∈ Set.Icc 0 1 :=
  sum_range_neg_one_pow_mul_mem_Icc antitone_const (fun _ => zero_le_one) L

-- The partial sums `1 - 1/2 + 1/3 - ⋯` of the alternating harmonic series lie in `[0, 1]`.
example (L : ℕ) : ∑ j ∈ Finset.range L, (-1 : ℝ) ^ j * (1 / (j + 1)) ∈ Set.Icc 0 1 := by
  have h := sum_range_neg_one_pow_mul_mem_Icc (f := fun j : ℕ => 1 / ((j : ℝ) + 1))
    (fun i j hij => by dsimp only; gcongr) (fun j => by positivity) L
  simpa using h

-- Over an interval the bound `f m` of `abs_sum_Ico_neg_one_pow_mul_le` is attained by a single
-- term: over `[3, 4)` the sum is `-f 3 = -1/4`.
example : |∑ k ∈ Finset.Ico (3 : ℕ) 4, (-1 : ℝ) ^ k * (1 / ((k : ℝ) + 1))| = 1 / 4 := by
  norm_num

-- An empty interval `[5, 3)` is allowed.
example {f : ℕ → ℝ} (hf : Antitone f) (hf0 : ∀ k, 0 ≤ f k) :
    |∑ k ∈ Finset.Ico 5 3, (-1 : ℝ) ^ k * f k| ≤ f 5 :=
  abs_sum_Ico_neg_one_pow_mul_le hf hf0 5 3

-- Nonnegativity is needed: the antitone sequence `f k = -k` has `f 0 = 0`, but its alternating
-- sum over `[0, 2)` is `0 + 1 = 1`.
example : |∑ k ∈ Finset.Ico (0 : ℕ) 2, (-1 : ℝ) ^ k * (-(k : ℝ))| = 1 := by
  norm_num [Finset.sum_range_succ]

-- Test section: the alternating sums of floor quotients.

-- `b k = k + 1` and `ν = 0`: the floor quotients `⌊n / (k + 1)⌋` for `k ≤ n` (Dent and Shor's
-- floor sequence). The hypotheses of the main theorem are satisfiable.
example : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    |(∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - 0),
          (⌊((n : ℝ) - 0) / ((k : ℝ) + 1)⌋ : ℝ) * (-1) ^ k) -
        n * ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - 0),
          (-1) ^ k / ((k : ℝ) + 1)| ≤ C * Real.sqrt n :=
  alternating_sum_floor_div_eq_add_bigO 0 le_rfl zero_lt_one (fun k => (k : ℝ) + 1)
    (fun i j hij => by simpa using hij) (fun k => by simp) (fun k => by simp)

-- A positive offset `ν = 1/2` with `b k = 2 k + 1`, with the explicit constant `6`.
example (n : ℕ) (hn : 1 ≤ n) :
    |(∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - 1 / 2),
          (⌊((n : ℝ) - 1 / 2) / (2 * k + 1)⌋ : ℝ) * (-1) ^ k) -
        n * ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - 1 / 2),
          (-1) ^ k / (2 * (k : ℝ) + 1)| ≤ 6 * Real.sqrt n :=
  abs_sub_le_six_mul_sqrt (b := fun k => 2 * (k : ℝ) + 1) (by norm_num) (by norm_num)
    (fun i j hij => show 2 * (i : ℝ) + 1 ≤ 2 * j + 1 by gcongr)
    (fun k => show (1 : ℝ) ≤ 2 * k + 1 by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    (fun k => show (k : ℝ) ≤ 2 * k + 1 by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hn

-- The explicit bound needs only a monotone sequence: `b k = max 1 k` has `b 0 = b 1 = 1`, so it
-- is not strictly increasing.
example (n : ℕ) (hn : 1 ≤ n) :
    |(∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - 0),
          (⌊((n : ℝ) - 0) / max 1 (k : ℝ)⌋ : ℝ) * (-1) ^ k) -
        n * ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - 0),
          (-1) ^ k / max 1 (k : ℝ)| ≤ 6 * Real.sqrt n :=
  abs_sub_le_six_mul_sqrt (b := fun k => max 1 (k : ℝ)) le_rfl zero_lt_one
    (fun _ _ hij => max_le_max le_rfl (Nat.cast_le.2 hij)) (fun _ => le_max_left _ _)
    (fun _ => le_max_right _ _) hn

-- The range of summation `k ≤ n - ν`: at `n = 4` it is `k ≤ 4` for `ν = 0` and `k ≤ 3` for
-- `ν = 1/2`.
example :
    (Finset.range (4 + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (4 : ℕ) - 0) = Finset.range 5 := by
  refine Finset.filter_true_of_mem fun k hk => ?_
  have : k ≤ 4 := by simpa [Nat.lt_succ_iff] using hk
  simpa using (by exact_mod_cast this : (k : ℝ) ≤ 4)

example :
    (Finset.range (4 + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (4 : ℕ) - 1 / 2) =
      Finset.range 4 := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    have : (k : ℝ) < 4 := by push_cast at h; linarith
    exact_mod_cast this
  · intro h
    refine ⟨by omega, ?_⟩
    have : (k : ℝ) ≤ 3 := by exact_mod_cast (by omega : k ≤ 3)
    push_cast
    linarith

-- At `n = 4`, `ν = 0`, `b k = k + 1`: the floor sum is `4 - 2 + 1 - 1 + 0 = 2` (the number of
-- odd values among `⌊4 / k⌋`, `1 ≤ k ≤ 4`) and the main term is
-- `4 * (1 - 1/2 + 1/3 - 1/4 + 1/5) = 47/15`, so the difference is `17/15`.
example :
    |(∑ k ∈ (Finset.range (4 + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (4 : ℕ) - 0),
          (⌊(((4 : ℕ) : ℝ) - 0) / ((k : ℝ) + 1)⌋ : ℝ) * (-1) ^ k) -
        ((4 : ℕ) : ℝ) *
          ∑ k ∈ (Finset.range (4 + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (4 : ℕ) - 0),
            (-1) ^ k / ((k : ℝ) + 1)| = 17 / 15 := by
  have hS : (Finset.range (4 + 1)).filter (fun k : ℕ => (k : ℝ) ≤ (4 : ℕ) - 0) =
      Finset.range 5 := by
    refine Finset.filter_true_of_mem fun k hk => ?_
    have : k ≤ 4 := by simpa [Nat.lt_succ_iff] using hk
    simpa using (by exact_mod_cast this : (k : ℝ) ≤ 4)
  rw [hS]
  norm_num [Finset.sum_range_succ]

end MathlibExtTest.AlternatingSumFloorDiv
