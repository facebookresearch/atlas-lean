/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: extracted the general estimates, narrowed imports, consolidated the
two exponential estimates, and added boundary and importing-client tests.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Bounds on partial sums of binomial coefficients

For `0 ≤ x ≤ 1` and `r ≤ D`, multiplying the partial binomial sum by `x ^ r`
gives a quantity at most `(1 + x) ^ D`, hence at most `exp (D * x)`.
Choosing `x = r / D` gives the counting bound `(3 * D / r) ^ r` when `r > 0`.

Adapted from `eth/proof/rates/ClauseBound/Rec/Few.lean` and
`eth/proof/machines/StepMachines/Math/SparsifyCount.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
The exponential estimate here also covers `x = 0`; the source's version in `SparsifyCount`
assumes `0 < x`. The sum and its summands are represented directly using Mathlib APIs.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Real

open Finset

/-- A weighted partial binomial sum is bounded by the full binomial expansion. -/
theorem pow_mul_sum_choose_le {D r : ℕ} (hr : r ≤ D) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ r * ∑ j ∈ range (r + 1), (D.choose j : ℝ) ≤ (x + 1) ^ D := by
  rw [add_pow, mul_sum]
  calc
    ∑ j ∈ range (r + 1), x ^ r * (D.choose j : ℝ) ≤
        ∑ j ∈ range (r + 1), x ^ j * 1 ^ (D - j) * (D.choose j : ℝ) := by
      refine sum_le_sum fun j hj => ?_
      rw [one_pow, mul_one]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hx0 hx1 (Nat.lt_succ_iff.mp (mem_range.mp hj)))
        (Nat.cast_nonneg _)
    _ ≤ ∑ j ∈ range (D + 1), x ^ j * 1 ^ (D - j) * (D.choose j : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.succ_le_succ hr))
        fun j _ _ => by positivity

/-- Exponential bound on the weighted partial binomial sum, including the zero-weight boundary. -/
theorem pow_mul_sum_choose_le_exp {D r : ℕ} (hr : r ≤ D) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ r * ∑ j ∈ range (r + 1), (D.choose j : ℝ) ≤ exp ((D : ℝ) * x) := by
  calc
    x ^ r * ∑ j ∈ range (r + 1), (D.choose j : ℝ) ≤ (x + 1) ^ D :=
      pow_mul_sum_choose_le hr hx0 hx1
    _ ≤ exp x ^ D := pow_le_pow_left₀ (by positivity) (add_one_le_exp x) D
    _ = exp ((D : ℝ) * x) := (exp_nat_mul x D).symm

/-- For `1 ≤ r ≤ D`, the number of subsets of size at most `r` is at most `(3 * D / r) ^ r`. -/
theorem sum_choose_le_pow {D r : ℕ} (hr0 : 1 ≤ r) (hrD : r ≤ D) :
    (∑ j ∈ range (r + 1), (D.choose j : ℝ)) ≤ (3 * D / r) ^ r := by
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  have hD : (0 : ℝ) < D := by exact_mod_cast lt_of_lt_of_le (by omega : 0 < r) hrD
  have hx0 : (0 : ℝ) < r / D := by positivity
  have hx1 : (r : ℝ) / D ≤ 1 := (div_le_one hD).mpr (by exact_mod_cast hrD)
  have hbound : ((r : ℝ) / D + 1) ^ D ≤ 3 ^ r := by
    calc
      ((r : ℝ) / D + 1) ^ D ≤ exp ((r : ℝ) / D) ^ D :=
        pow_le_pow_left₀ (by positivity) (add_one_le_exp _) D
      _ = exp 1 ^ r := by
        rw [← exp_nat_mul, ← exp_nat_mul, mul_one, mul_div_cancel₀ _ hD.ne']
      _ ≤ 3 ^ r := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_three.le r
  have h := (pow_mul_sum_choose_le hrD hx0.le hx1).trans hbound
  have heq : (3 * (D : ℝ) / r) ^ r = 3 ^ r / ((r : ℝ) / D) ^ r := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [heq, le_div_iff₀ (by positivity), mul_comm]
  exact h

end Real
