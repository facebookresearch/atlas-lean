/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for network calculus concatenation
-/

module

public import CSLibExt.Algorithms.Networking.NetworkCalculus
public import CSLibExt.Algorithms.Networking.NetworkCalculusConcatenation
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.Monotone.Defs

/-!
## Tests for the concatenation of service curves (Section 1.4.3)

Intserv two-node example, per-node comparison, single-node reduction,
order swap, zero-latency pair, and unsustainable rate.
-/

@[expose] public section

namespace Cslib.Algorithms.Networking.NetworkCalculus

open scoped NNReal ENNReal

/-- Two-node Intserv example: rates `2, 3`, latencies `1, 2`, token bucket
`r = 1, b = 4`; the end-to-end bound is `T₁ + T₂ + b / min = 3 + 2 = 5`. -/
theorem concat_intserv_two_node :
    hdev (tokenBucket 1 4) (convCurve (rateLatency 2 1) (rateLatency 3 2))
      = 5 := by
  have hmin : min (2 : ℝ≥0) 3 = 2 := min_eq_left (by norm_num)
  rw [convCurve_rateLatency, hmin]
  rw [hdev_tokenBucket_rateLatency (by norm_num : (1 : ℝ≥0) ≤ 2)
    (by norm_num : (0 : ℝ≥0) < 2) (Or.inl (by norm_num))]
  have h5 : ((1 + 2 + 4 / 2 : ℝ≥0)) = 5 := by norm_num
  rw [h5]
  exact ENNReal.coe_ofNat 5

/-- Per-node iteration charges the burst twice, so its closed form strictly
exceeds the end-to-end bound: `5 < 2 + 5 / 3 + 3`. -/
theorem concat_intserv_per_node_exceeds :
    (5 : ℝ≥0∞) < ((2 + 5 / 3 + 3 : ℝ≥0) : ℝ≥0∞) := by
  have h : (5 : ℝ≥0) < 2 + 5 / 3 + 3 := by norm_num
  rw [← ENNReal.coe_ofNat 5]
  exact ENNReal.coe_lt_coe.mpr h

/-- Single-node reduction (boundary): with `T₂ = 0` and `R₂ ≥ R₁`, the
end-to-end bound equals the one-node bound `T₁ + b / R₁`. -/
theorem concat_single_node_reduction {r b R₁ R₂ T₁ : ℝ≥0} (hle : R₁ ≤ R₂)
    (hr : r ≤ R₁) (hR : 0 < R₁) (hpos : 0 < r ∨ 0 < b) :
    hdev (tokenBucket r b) (convCurve (rateLatency R₁ T₁) (rateLatency R₂ 0))
      = ((T₁ + b / R₁ : ℝ≥0) : ℝ≥0∞) := by
  have hmin : min R₁ R₂ = R₁ := min_eq_left hle
  rw [convCurve_rateLatency, hmin, add_zero]
  exact hdev_tokenBucket_rateLatency hr hR hpos

/-- Order swap on the Intserv rates leaves the concatenated curve unchanged. -/
theorem concat_order_swap_example :
    convCurve (rateLatency 2 1) (rateLatency 3 2)
      = convCurve (rateLatency 3 2) (rateLatency 2 1) := by
  exact convCurve_comm _ _

/-- Zero-latency pair: `β_{2,0} ⊗ β_{3,0} = β_{2,0}`. -/
theorem concat_zero_latency_pair :
    convCurve (rateLatency 2 0) (rateLatency 3 0) = rateLatency 2 0 := by
  have hmin : min (2 : ℝ≥0) 3 = 2 := min_eq_left (by norm_num)
  rw [convCurve_rateLatency, hmin, add_zero]

/-- Unsustainable rate: `r > min R₁ R₂` gives top horizontal deviation
against the concatenated curve. -/
theorem concat_unsustainable_rate_top {r b R₁ R₂ T₁ T₂ : ℝ≥0}
    (h : min R₁ R₂ < r) :
    hdev (tokenBucket r b) (convCurve (rateLatency R₁ T₁) (rateLatency R₂ T₂))
      = ⊤ := by
  rw [convCurve_rateLatency]
  exact hdev_top_of_rate h

end Cslib.Algorithms.Networking.NetworkCalculus
