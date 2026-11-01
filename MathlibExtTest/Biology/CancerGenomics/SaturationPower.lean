/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.CancerGenomics.SaturationPower
import Mathlib.Tactic.NormNum

/-! Tests for the binomial saturation-power model: a degenerate cohort, the existence of a
90%-power cohort size for concrete rates, and the Lawrence et al. parameter conditions. -/

namespace MathlibExtTest.Biology.CancerGenomics.SaturationPower

open Finset MathlibExt.Biology.CancerGenomics.SaturationPower
  MathlibExt.Biology.CancerGenomics.DetectionPower

/-- With no patients the only count is `0`, its p-value is `1`, and at level `γ = 1` the power
is `1`. -/
example : saturationPower 0 (1 / 10) (1 / 5) 1 = 1 := by
  rw [saturationPower, range_one, sum_filter, sum_singleton, upperTail_zero]
  norm_num [binomPmf]

/-- At level `γ < 1` an empty cohort has power `0`. -/
example : saturationPower 0 (1 / 10) (1 / 5) (1 / 2) = 0 := by
  rw [saturationPower, range_one, sum_filter, sum_singleton, upperTail_zero]
  norm_num

/-- A 90%-power cohort size exists for a background `p₀ = 0.1`, signal `p₁ = 0.2` and the
Lawrence et al. level `0.1 / 20000`. -/
example : ∃ N₀, ∀ N ≥ N₀, (9 / 10 : ℝ) ≤ saturationPower N (1 / 10) (1 / 5) (1 / 200000) :=
  eventually_le_saturationPower (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The Lawrence et al. background for `L = 1500`, `μ f_g = 3.9 × 10⁻⁶` is a probability below
one, and a driver at `r = 0.02` with miss rate `0.1` raises it. -/
example : 0 ≤ lawrenceP0 (39 / 10000000) 1 1500 ∧ lawrenceP0 (39 / 10000000) 1 1500 < 1 :=
  lawrenceP0_mem (by norm_num) (by norm_num) (by norm_num)

example : lawrenceP0 (39 / 10000000) 1 1500 <
    lawrenceP1 (lawrenceP0 (39 / 10000000) 1 1500) (1 / 50) (1 / 10) :=
  lawrenceP0_lt_lawrenceP1 (by norm_num) (by norm_num)

end MathlibExtTest.Biology.CancerGenomics.SaturationPower
