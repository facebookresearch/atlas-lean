/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.Kronecker
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tests for Kronecker's lemma

* The geometric series `∑ (1 / 2) ^ k` converges, so with the weights `k + 1` the weighted means
  `(∑_{k < n} (k + 1) (1 / 2) ^ k) / (n + 1)` tend to `0`.
* Nondecreasing weights that are not strictly increasing: `⌊k / 2⌋ + 1`.
* The weights `(k + 1)²` used by the almost-sure approachability and regret-matching proofs.
-/

namespace MathlibExtTest.Kronecker

open Filter Topology

/-- Kronecker's lemma for the geometric series with the weights `k + 1`. -/
example : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ((k : ℝ) + 1) * (1 / 2) ^ k) /
    ((n : ℝ) + 1)) atTop (𝓝 0) :=
  MetaMathlibExt.tendsto_sum_range_mul_div_of_tendsto (b := fun k : ℕ => (k : ℝ) + 1)
    (fun a b hab => by simpa using hab) (tendsto_atTop_add_const_right _ 1
      tendsto_natCast_atTop_atTop) hasSum_geometric_two.tendsto_sum_nat

/-- Kronecker's lemma holds for nondecreasing weights that are not strictly increasing: the
weights `⌊k / 2⌋ + 1` repeat each value twice. -/
example : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ((k / 2 : ℕ) + 1 : ℝ) * (1 / 2) ^ k) /
    ((n / 2 : ℕ) + 1 : ℝ)) atTop (𝓝 0) :=
  MetaMathlibExt.tendsto_sum_range_mul_div_of_tendsto (b := fun k : ℕ => ((k / 2 : ℕ) + 1 : ℝ))
    (fun a c hac => by
      have : ((a / 2 : ℕ) : ℝ) ≤ (c / 2 : ℕ) := by exact_mod_cast Nat.div_le_div_right hac
      dsimp only
      linarith)
    (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp
      (Nat.tendsto_div_const_atTop two_ne_zero))) hasSum_geometric_two.tendsto_sum_nat

/-- The case `b k = (k + 1)²` for the geometric series. -/
example : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 2 * (1 / 2) ^ k) /
    ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) :=
  MetaMathlibExt.tendsto_sum_range_add_one_sq_mul_div_of_tendsto
    hasSum_geometric_two.tendsto_sum_nat

end MathlibExtTest.Kronecker
