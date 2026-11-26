/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumExistsTailEqPseudoGreedyExpansion
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for tails that are pseudo-greedy expansions -/

namespace MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumExistsTailEqPseudoGreedyExpansion

open MetaMathlibExt Filter Topology

-- The sequence `2 ^ 2 ^ n` has ratio exactly `1` and a convergent reciprocal sum.
/-- Ratio of successive terms of `2 ^ 2 ^ ·` is constantly `1`. -/
private theorem ratio_two_pow_two_pow (n : ℕ) :
    ((2 ^ 2 ^ n : ℕ) : ℝ) ^ 2 / ((2 ^ 2 ^ (n + 1) : ℕ) : ℝ) = 1 := by
  have e : 2 ^ n * 2 = 2 ^ (n + 1) := (pow_succ 2 n).symm
  simp only [Nat.cast_pow, Nat.cast_two]
  rw [← pow_mul, e]
  exact div_self (pow_ne_zero _ (show (2 : ℝ) ≠ 0 by norm_num))

/-- The reciprocal sum of `2 ^ 2 ^ ·` converges by comparison with `(1 / 2) ^ n`. -/
private theorem summable_one_div_two_pow_two_pow :
    Summable (fun n => 1 / ((2 ^ 2 ^ n : ℕ) : ℝ)) := by
  have hsG := summable_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hsG
  intro n
  rw [Nat.cast_pow, Nat.cast_two, div_pow, one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_right₀ (by norm_num)
  exact Nat.lt_two_pow_self.le

-- Applied to `2 ^ 2 ^ ·`: some tail is the pseudo-greedy expansion of its sum.
example : ∃ N : ℕ, ((2 ^ 2 ^ N : ℕ) : ℤ)
    = pseudoGreedyExpansion (∑' k, 1 / ((2 ^ 2 ^ (N + k) : ℕ) : ℝ)) 0 := by
  have hpos : ∀ n, 0 < (2 ^ 2 ^ n : ℕ) := fun n => by positivity
  have hratio : Tendsto (fun n => ((2 ^ 2 ^ n : ℕ) : ℝ) ^ 2 / ((2 ^ 2 ^ (n + 1) : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have heq : (fun n => ((2 ^ 2 ^ n : ℕ) : ℝ) ^ 2 / ((2 ^ 2 ^ (n + 1) : ℕ) : ℝ))
        = fun _ => (1 : ℝ) :=
      funext ratio_two_pow_two_pow
    rw [heq]
    exact tendsto_const_nhds
  obtain ⟨N, htail, -⟩ :=
    exists_tail_eq_pseudoGreedyExpansion hpos hratio summable_one_div_two_pow_two_pow
  exact ⟨N, htail 0⟩

end MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumExistsTailEqPseudoGreedyExpansion
