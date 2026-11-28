/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumConjectureEquivalence

/-!
# Tests for the pseudo-greedy conjecture equivalence

Check the zero gaps of the expansion of `1` and the recurrence of the sequence obtained
by prepending `2` to it. The resulting sequence is positive, has reciprocal sum `3/2`,
and its square ratio tends to `1`. Its first step fails the recurrence, but every later
step satisfies it. These checks are independent of the equivalence theorem.
-/

open Filter Topology MetaMathlibExt

namespace MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumConjectureEquivalence

private theorem one_gap (n : ℕ) : pseudoGreedyGap 1 n = 0 := by
  induction n with
  | zero => exact pseudoGreedyGap_one_zero
  | succ n ih => exact pseudoGreedyGap_succ_eq_zero zero_lt_one ih

private noncomputable def b : ℕ → ℕ
  | 0 => 2
  | n + 1 => (pseudoGreedyExpansion 1 n).toNat

private theorem b_pos : ∀ n, 0 < b n
  | 0 => by decide
  | n + 1 => by
    change 0 < (pseudoGreedyExpansion 1 n).toNat
    have := pseudoGreedyExpansion_pos zero_lt_one n
    omega

private theorem b_succ_cast (n : ℕ) : (b (n + 1) : ℝ) = (pseudoGreedyExpansion 1 n : ℝ) := by
  rw [b, ← Int.cast_natCast, Int.toNat_of_nonneg (pseudoGreedyExpansion_pos zero_lt_one n).le]

private theorem b_tail_step (n : ℕ) :
    (b (n + 1 + 1) : ℝ) = (b (n + 1) : ℝ) ^ 2 - b (n + 1) + 1 := by
  simpa only [b_succ_cast, one_gap, sub_zero, div_one, one_mul] using
    pseudoGreedyExpansion_succ_eq zero_lt_one n

private theorem b_tail_sum : HasSum (fun n => 1 / (b (n + 1) : ℝ)) (1 : ℝ) := by
  simpa only [b_succ_cast] using hasSum_one_div_pseudoGreedyExpansion zero_lt_one

private theorem b_sum : HasSum (fun n => 1 / (b n : ℝ)) ((3 / 2 : ℚ) : ℝ) := by
  apply (hasSum_nat_add_iff' 1).mp
  convert b_tail_sum using 1
  norm_num [b]

private theorem b_ratio : Tendsto (fun n => (b n : ℝ) ^ 2 / b (n + 1)) atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hu := b_tail_sum.summable.tendsto_atTop_zero
  have h := ((hu.const_sub 1).add (hu.pow 2)).inv₀ (by norm_num)
  simp only [sub_zero, zero_pow two_ne_zero, add_zero, inv_one] at h
  refine h.congr fun n => ?_
  have hne : (b (n + 1) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (b_pos _)).ne'
  have hnorm : 1 - 1 / (b (n + 1) : ℝ) + (1 / (b (n + 1) : ℝ)) ^ 2 =
      (b (n + 1 + 1) : ℝ) / (b (n + 1) : ℝ) ^ 2 := by
    rw [b_tail_step]
    field_simp [hne]
  change (1 - 1 / (b (n + 1) : ℝ) + (1 / (b (n + 1) : ℝ)) ^ 2)⁻¹ = _
  rw [hnorm, inv_div]

private theorem expansion_one_two : pseudoGreedyExpansion 1 2 = 7 := by
  have h := pseudoGreedyExpansion_succ_eq zero_lt_one 1
  rw [one_gap 1, one_gap 2, pseudoGreedyExpansion_one_one] at h
  norm_num at h
  exact_mod_cast h

example : 0 < pseudoGreedyExpansion 1 2 := by
  rw [expansion_one_two]
  norm_num

example : b 1 ≠ b 0 ^ 2 - b 0 + 1 := by
  norm_num [b, pseudoGreedyExpansion_one_zero]

example : ∀ n, b (n + 1 + 1) = b (n + 1) ^ 2 - b (n + 1) + 1 := by
  intro n
  apply (Nat.cast_inj (R := ℝ)).mp
  simpa only [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero _), Nat.cast_pow,
    Nat.cast_one] using b_tail_step n

-- Client of the forward implication at a sequence with a nonsatisfying first step.
example
    (hconj : ∀ r : ℚ, 0 < r → Tendsto (pseudoGreedyGap r) atTop (𝓝 0) →
      ∀ᶠ n in atTop, pseudoGreedyGap r n = 0) :
    ∀ᶠ n in atTop, b (n + 1) = b n ^ 2 - b n + 1 :=
  pseudoGreedy_conjecture_iff_erdos_graham_question.mp hconj b b_pos b_ratio ⟨3 / 2, b_sum⟩

-- Client of the reverse implication at the rational input `1`.
example
    (hquestion : ∀ a : ℕ → ℕ, (∀ n, 0 < a n) →
      Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1) →
      (∃ q : ℚ, HasSum (fun n => 1 / (a n : ℝ)) q) →
      ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1) :
    ∀ᶠ n in atTop, pseudoGreedyGap 1 n = 0 := by
  have hgap : pseudoGreedyGap 1 = fun _ => 0 := funext one_gap
  simpa only [Rat.cast_one] using
    pseudoGreedy_conjecture_iff_erdos_graham_question.mpr hquestion 1 zero_lt_one (by
      simpa only [Rat.cast_one, hgap] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

end MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumConjectureEquivalence
