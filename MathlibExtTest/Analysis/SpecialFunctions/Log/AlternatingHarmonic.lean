/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.AlternatingHarmonic

/-!
# Tests for the alternating harmonic series
-/

open scoped Topology

namespace Real

/-- The alternating harmonic series converges to `log 2`. -/
example : Filter.Tendsto (fun k => ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i / (↑i + 1))
    Filter.atTop (𝓝 (Real.log 2)) :=
  Real.tendsto_sum_alternating_harmonic

/-- The alternating harmonic series is not absolutely summable. -/
example : ¬ Summable (fun n : ℕ => |(-1 : ℝ) ^ n / (↑n + 1)|) :=
  Real.not_summable_abs_alternating_harmonic

/-- Sanity check: the first partial sums bracket `log 2`, as the alternating
series test predicts (`1 - 1/2 = 1/2 ≤ log 2 ≤ 1`). -/
example : (1 : ℝ) / 2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  have hconv : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) =
        (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i : ℝ) + 1)⁻¹) := by
    intro n
    apply Finset.sum_congr rfl
    intro i _
    rw [div_eq_mul_inv]
  have hanti : Antitone (fun n : ℕ => ((↑n + 1 : ℝ))⁻¹) := by
    intro a b hab
    exact inv_anti₀ (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hab 1)
  constructor
  · have hle := hanti.alternating_series_le_tendsto
      Real.tendsto_sum_alternating_harmonic 1
    rw [← hconv] at hle
    simp only [mul_one] at hle
    have h0 : (∑ i ∈ Finset.range 2, (-1 : ℝ) ^ i / (↑i + 1)) = (1 : ℝ) / 2 := by
      norm_num [Finset.sum_range_succ]
    rw [h0] at hle
    exact hle
  · have hle := hanti.tendsto_le_alternating_series
      Real.tendsto_sum_alternating_harmonic 0
    rw [← hconv] at hle
    simp only [mul_zero, zero_add] at hle
    have h0 : (∑ i ∈ Finset.range 1, (-1 : ℝ) ^ i / (↑i + 1)) = (1 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    rw [h0] at hle
    exact hle

#print axioms Real.tendsto_sum_alternating_harmonic
#print axioms Real.not_summable_abs_alternating_harmonic

end Real
