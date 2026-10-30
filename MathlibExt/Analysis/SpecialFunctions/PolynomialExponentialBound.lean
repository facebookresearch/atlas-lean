/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: exposed the source's explicit constant as a bound for nonnegative
real inputs and retained the natural-input, base-two exponential estimate.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Uniform polynomial bounds by exponentials

For a positive exponential rate, a fixed power is bounded by an explicit natural multiple
of the exponential on the entire nonnegative half-line.

Adapted from `eth/proof/machines/StepMachines/Math/SatArith.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
The source uses natural inputs and base two; the first theorem separately generalizes the
input to a nonnegative real and exposes the constant used in its proof.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Real

/-- An explicit natural multiple of a positive-rate exponential bounds a fixed power. -/
theorem pow_le_natCeil_mul_exp (n : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x ^ n ≤ (⌈(n.factorial : ℝ) / c ^ n⌉₊ : ℝ) * exp (c * x) := by
  have h := pow_div_factorial_le_exp (x := c * x) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have heq : x ^ n = (n.factorial / c ^ n) * ((c * x) ^ n / n.factorial) := by
    rw [mul_pow]
    field_simp
  rw [heq]
  exact mul_le_mul (Nat.le_ceil _) h (by positivity) (by positivity)

/-- A single natural constant bounds a fixed power by a positive-rate exponential. -/
theorem exists_nat_pow_le_mul_exp (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℕ, ∀ x : ℝ, 0 ≤ x → x ^ n ≤ C * exp (c * x) :=
  ⟨⌈(n.factorial : ℝ) / c ^ n⌉₊, fun _ hx => pow_le_natCeil_mul_exp n hc hx⟩

/-- The source estimate: a natural-input polynomial is bounded by a base-two exponential. -/
theorem exists_nat_pow_le_mul_two_rpow (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℕ, ∀ x : ℕ, (x : ℝ) ^ n ≤ C * (2 : ℝ) ^ (c * x) := by
  have hk : 0 < c * log 2 := mul_pos hc (log_pos one_lt_two)
  obtain ⟨C, hC⟩ := exists_nat_pow_le_mul_exp n hk
  refine ⟨C, fun x => ?_⟩
  calc
    (x : ℝ) ^ n ≤ C * exp ((c * log 2) * x) := hC _ (Nat.cast_nonneg _)
    _ = C * (2 : ℝ) ^ (c * x) := by
      congr 1
      rw [rpow_def_of_pos two_pos]
      congr 1
      ring

end Real
