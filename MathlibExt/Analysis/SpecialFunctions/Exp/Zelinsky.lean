/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Zelinsky's exponential lower bound for a quadratic

On `[0, 1/11]`, `exp (x + 2 * x ^ 2 / 5)` bounds `1 + x + x ^ 2` from below,
with equality exactly at zero.
-/

namespace MetaMathlibExt

/-- **Exponential lower bound for $1 + x + x^2$ on $[0, 1/11]$.** For every real $x$ with
$0 \le x \le 1/11$, $\exp(x + 2x^2/5) \le 1 + x + x^2$, with equality if and only if $x = 0$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 3 (`integers-2025-A59-lem-3`). -/
public theorem exp_add_two_fifths_sq_le_one_add_add_sq
    (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 11) :
    Real.exp (x + 2 * x ^ 2 / 5) ≤ 1 + x + x ^ 2 ∧
      (Real.exp (x + 2 * x ^ 2 / 5) = 1 + x + x ^ 2 ↔ x = 0) := by
  rcases h0.eq_or_lt with rfl | hx
  · simp
  have hstrict : Real.exp (x + 2 * x ^ 2 / 5) < 1 + x + x ^ 2 := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).mp
    rw [add_assoc]
    refine lt_of_le_of_lt ?_ (Real.lt_log_one_add_of_pos (by positivity))
    apply (le_div_iff₀ (by positivity)).mpr
    -- After clearing the denominator, the difference is x² (1 - 7x - 2x²) / 5.
    have hfactor : 0 ≤ 1 - 7 * x - 2 * x ^ 2 := by
      nlinarith [mul_nonneg hx.le (show 0 ≤ 1 - x by linarith)]
    nlinarith [mul_nonneg (sq_nonneg x) hfactor]
  exact ⟨hstrict.le, iff_of_false hstrict.ne hx.ne'⟩

end MetaMathlibExt
