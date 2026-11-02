/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.IntegrationSubcritical
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.IntegrationSubcritical`

* `isc_gronwall_lower` and `isc_gronwall_decay` for `f x = e^{2x}` (equality case of `f' ≥ 2 f`).
* `isc_summable_stretched_exp` at `α = δ = 1`.
* `isc_partial_sum_le` and `isc_rate_weaken` at small inputs.
-/

@[expose] public section

open StatMech.OSSS.IntegrationSubcritical

namespace MathlibExtTest.StatMech.Probability.OSSS.IntegrationSubcritical

theorem hd (x : ℝ) : HasDerivAt (fun y => Real.exp (2 * y)) (2 * Real.exp (2 * x)) x := by
  have h := ((hasDerivAt_id x).const_mul (2 : ℝ)).exp
  simp only [id, mul_one] at h
  rw [mul_comm]; exact h

example : Real.exp (2 * (1 - 0)) * Real.exp (2 * 0) ≤ Real.exp (2 * 1) :=
  isc_gronwall_lower 0 1 2 zero_le_one (fun y => Real.exp (2 * y)) _ (fun x _ => hd x)
    (fun _ _ => le_rfl)

example : Real.exp (2 * 0) ≤ Real.exp (2 * 1) * Real.exp (-(2 * (1 - 0))) :=
  isc_gronwall_decay 0 1 2 _ zero_le_one (fun y => Real.exp (2 * y)) _ (fun x _ => hd x)
    (fun _ _ => le_rfl) le_rfl

example : Summable (fun n : ℕ => Real.exp (-(1 * (n : ℝ) ^ (1 : ℝ)))) :=
  isc_summable_stretched_exp 1 1 one_pos one_pos

example (n : ℕ) : ∑ _k ∈ Finset.range n, (0 : ℝ) ≤ (0 : ℕ) * 1 + ∑' _ : ℕ, (0 : ℝ) :=
  isc_partial_sum_le (fun _ => 0) (fun _ => 0) 1 0 n (fun _ => zero_le_one) zero_le_one
    (fun _ => le_rfl) summable_zero (fun _ _ => le_rfl)

example : ((3 : ℕ) : ℝ) / 2 * 1 ≤ 3 :=
  isc_rate_weaken 3 1 3 1 2 one_pos (by norm_num) zero_le_one (by norm_num)

end MathlibExtTest.StatMech.Probability.OSSS.IntegrationSubcritical
