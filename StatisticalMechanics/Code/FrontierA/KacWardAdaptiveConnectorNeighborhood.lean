/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptivePatchedTurns
import Code.FrontierA.KacWardVertexNeighborhood









namespace StatMech.FrontierA

open Set

theorem kwHVConnectorCorner_eq_parts (a b : ℂ) :
    kwHVConnectorCorner a b = kwHorizontalPart b + kwVerticalPart a := by
  apply Complex.ext <;>
    simp [kwHVConnectorCorner, kwHorizontalPart, kwVerticalPart]

theorem kwVHConnectorCorner_eq_parts (a b : ℂ) :
    kwVHConnectorCorner a b = kwHorizontalPart a + kwVerticalPart b := by
  apply Complex.ext <;>
    simp [kwVHConnectorCorner, kwHorizontalPart, kwVerticalPart]

theorem KWAdaptiveConnectorData.corner_norm_le
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b) :
    ‖connector.corner‖ ≤ ‖a‖ + ‖b‖ := by
  rcases connector.axis_corner with h | h
  · rw [h, kwHVConnectorCorner_eq_parts]
    calc
      ‖kwHorizontalPart b + kwVerticalPart a‖ ≤
          ‖kwHorizontalPart b‖ + ‖kwVerticalPart a‖ := norm_add_le _ _
      _ ≤ ‖b‖ + ‖a‖ := add_le_add
        (norm_kwHorizontalPart_le b) (norm_kwVerticalPart_le a)
      _ = ‖a‖ + ‖b‖ := add_comm _ _
  · rw [h, kwVHConnectorCorner_eq_parts]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_kwHorizontalPart_le a) (norm_kwVerticalPart_le b))

theorem KWAdaptiveConnectorData.corner_mem_ball
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    {r : ℝ} (ha : ‖a‖ < r / 2) (hb : ‖b‖ < r / 2) :
    connector.corner ∈ Metric.ball (0 : ℂ) r := by
  rw [Metric.mem_ball, dist_zero_right]
  exact connector.corner_norm_le.trans_lt (by linarith)

theorem KWAdaptiveConnectorData.translated_closedLegs_subset_ball
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (v : ℂ) {r : ℝ} (hr : 0 < r)
    (ha : ‖a‖ < r / 2) (hb : ‖b‖ < r / 2) :
    segment ℝ (v + a) (v + connector.corner) ⊆ Metric.ball v r ∧
      segment ℝ (v + connector.corner) (v + b) ⊆ Metric.ball v r := by
  have ha' : v + a ∈ Metric.ball v r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left] using ha.trans (half_lt_self hr)
  have hb' : v + b ∈ Metric.ball v r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left] using hb.trans (half_lt_self hr)
  have hc' : v + connector.corner ∈ Metric.ball v r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left, Metric.mem_ball, dist_zero_right] using
      connector.corner_mem_ball ha hb
  exact ⟨(convex_ball v r).segment_subset ha' hc',
    (convex_ball v r).segment_subset hc' hb'⟩

end StatMech.FrontierA
