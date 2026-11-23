/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite weighted geometric sum

The partial sums of `∑ h / 2 ^ (h + 1)` have the closed form
`∑ h ∈ Finset.range k, h / 2 ^ (h + 1) = 1 - (k + 1) / 2 ^ k`, so every partial sum is
at most `1`.

## Main results

* `MathlibExt.sum_range_div_two_pow_succ_eq`: the closed form above.
* `MathlibExt.sum_range_div_two_pow_succ_le_one`: every partial sum is at most `1`.
* `MathlibExt.sum_range_div_two_pow_succ_mul_le`: the first `n` weights, each scaled by
  `n`, sum to at most `n`.
-/

@[expose] public section

namespace MathlibExt

/-- Closed form of the partial sums of `∑ h / 2 ^ (h + 1)`:
`∑ h ∈ range k, h / 2 ^ (h + 1) = 1 - (k + 1) / 2 ^ k`. -/
theorem sum_range_div_two_pow_succ_eq (k : ℕ) :
    ∑ h ∈ Finset.range k, (h : ℝ) / 2 ^ (h + 1) = 1 - (k + 1 : ℝ) / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- Every partial sum of `∑ h / 2 ^ (h + 1)` is at most `1`. -/
theorem sum_range_div_two_pow_succ_le_one (k : ℕ) :
    ∑ h ∈ Finset.range k, (h : ℝ) / 2 ^ (h + 1) ≤ 1 := by
  rw [sum_range_div_two_pow_succ_eq]
  have hnonneg : 0 ≤ (k + 1 : ℝ) / 2 ^ k := by positivity
  linarith

/-- The first `n` weights `h / 2 ^ (h + 1)`, each scaled by `n`, sum to at most `n`. -/
theorem sum_range_div_two_pow_succ_mul_le (n : ℕ) :
    ∑ h ∈ Finset.range n, ((n : ℝ) / 2 ^ (h + 1)) * h ≤ n := by
  have hcongr : (∑ h ∈ Finset.range n, ((n : ℝ) / 2 ^ (h + 1)) * (h : ℝ))
      = ∑ h ∈ Finset.range n, (n : ℝ) * ((h : ℝ) / 2 ^ (h + 1)) := by
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hcongr, ← Finset.mul_sum]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc (n : ℝ) * ∑ h ∈ Finset.range n, (h : ℝ) / 2 ^ (h + 1)
      ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left (sum_range_div_two_pow_succ_le_one n) hn
    _ = (n : ℝ) := mul_one _

end MathlibExt
