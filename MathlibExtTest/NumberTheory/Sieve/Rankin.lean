/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Sieve.Rankin
import MathlibExt.NumberTheory.PrimeCounting.Mertens

/-!
# Tests for Rankin's trick
-/

@[expose] public section

open Nat Finset

example : (10 : ℕ).primesLE = {2, 3, 5, 7} := by decide

-- Boundary `p = 1` of the elementary estimate: `1 ≤ 1 + e · 0`.
example {z : ℝ} (hz : 0 < Real.log z) (h1z : 1 ≤ z) :
    (1 : ℝ) ^ (1 / Real.log z - 1) ≤ (1 : ℝ)⁻¹ + Real.exp 1 * (1 / Real.log z) *
      (Real.log 1 / 1) :=
  Real.rpow_inv_log_sub_one_le le_rfl h1z hz

-- Rankin's smooth-number bound at `δ = 1`: the `3`-smooth numbers up to `10` are
-- `1, 2, 4, 8`, and `4 ≤ 10 · 2`.
example : (smoothNumbersUpTo 10 3).card = 4 := by decide +kernel
example : ((smoothNumbersUpTo 10 3).card : ℝ) ≤
    (10 : ℝ) ^ (1 : ℝ) * ∏ p ∈ (3 : ℕ).primesBelow, (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹ := by
  exact_mod_cast card_smoothNumbersUpTo_le_rpow_mul_prod 10 3 one_pos

/-! ### The weighted bounds have satisfiable hypotheses

For `P = ⊤` and `ω ≡ 1` (dimension `κ = 1`), the hypothesis is Mertens' first theorem. -/

example : ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ z : ℝ, 3 ≤ z →
    ∑ d ∈ (siftingPrimorial (fun _ => True) ⌊z⌋₊).divisors with ((d : ℕ) : ℝ) ≤ t,
        ∏ _p ∈ d.primeFactors, (1 : ℝ) ≤
      C * t * Real.log z ^ (1 : ℝ) * Real.exp (-(Real.log t / Real.log z)) := by
  refine sum_divisors_siftingPrimorial_le (fun _ => True) (fun _ => 1) 1 (Real.log 4 + 6)
    (fun _ => zero_le_one) fun z hz => ?_
  have h := Chebyshev.sum_primesLE_log_div_le ⌊z⌋₊
  have h1 : (1 : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ z by
    norm_num; linarith)
  have hfl : Real.log ⌊z⌋₊ ≤ Real.log z :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  simp only [Finset.filter_true, one_mul]
  linarith
