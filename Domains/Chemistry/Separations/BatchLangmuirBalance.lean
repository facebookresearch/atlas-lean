/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# Batch adsorber with a Langmuir isotherm

The concentration-form isotherm is stipulated for a single solute in a liquid. The equation
in Monica Lamm and Laura Jarboe, *Chemical Engineering Separations: A Handbook for Students*,
§1.7, Equation 31.3, uses gas partial pressure; no identification of pressure with concentration
is used here. Competitive and nonideal adsorption are outside this model.
-/

namespace Chemistry.Separations

/-- In the stipulated liquid-phase Langmuir model, let `V > 0` be the liquid volume,
`c₀ ≥ 0` the initial solute concentration, `m ≥ 0` the mass of initially unloaded adsorbent,
`qMax > 0` the saturation loading, and `K ≥ 0` the affinity parameter (in inverse
concentration units).
For `q(c) = qMax * (K * c / (1 + K * c))`, the balance `V * (c₀ - c) = m * q(c)`
has exactly one root in `[0, c₀]`. Its fractional occupancy `q(c) / qMax` is in `[0, 1)`.
If `K = 0` or `m = 0`, the root is `c₀` and the total adsorbed amount `m * q(c)` is zero;
when `m = 0`, the formula for loading per unit mass need not vanish. -/
public theorem batchLangmuirBalance {V c₀ m qMax K : ℝ}
    (hV : 0 < V) (hc₀ : 0 ≤ c₀) (hm : 0 ≤ m) (hqMax : 0 < qMax) (hK : 0 ≤ K) :
    let q : ℝ → ℝ := fun c => qMax * (K * c / (1 + K * c))
    ∃ c ∈ Set.Icc 0 c₀, V * (c₀ - c) = m * q c ∧
      (∀ d ∈ Set.Icc 0 c₀, V * (c₀ - d) = m * q d → d = c) ∧
      q c / qMax ∈ Set.Ico 0 1 ∧
      (K = 0 ∨ m = 0 → c = c₀ ∧ m * q c = 0) := by
  intro q
  have hden {x : ℝ} (hx : 0 ≤ x) : 0 < 1 + K * x :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hK hx)
  have hq_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ q x :=
    mul_nonneg hqMax.le (div_nonneg (mul_nonneg hK hx) (hden hx).le)
  have hKc : Continuous (fun x : ℝ => K * x) := continuous_const.mul continuous_id
  have hq_cont : ContinuousOn q (Set.Icc 0 c₀) :=
    continuousOn_const.mul (hKc.continuousOn.div (continuousOn_const.add hKc.continuousOn)
      fun _ hx => (hden hx.1).ne')
  have hL_cont : Continuous (fun x : ℝ => V * (c₀ - x)) :=
    continuous_const.mul (continuous_const.sub continuous_id)
  have hleft : m * q 0 ≤ V * (c₀ - 0) := by
    simpa [q] using mul_nonneg hV.le hc₀
  have hright : V * (c₀ - c₀) ≤ m * q c₀ := by
    simpa only [sub_self, mul_zero] using mul_nonneg hm (hq_nonneg hc₀)
  obtain ⟨c, hc, hbalance⟩ : ∃ x ∈ Set.Icc 0 c₀, V * (c₀ - x) = m * q x :=
    isPreconnected_Icc.intermediate_value₂ (Set.right_mem_Icc.2 hc₀) (Set.left_mem_Icc.2 hc₀)
      hL_cont.continuousOn (continuousOn_const.mul hq_cont) hright hleft
  have hR_mono : MonotoneOn (fun x => m * q x) (Set.Icc 0 c₀) := by
    intro x hx y hy hxy
    have hfrac : K * x / (1 + K * x) ≤ K * y / (1 + K * y) := by
      apply (div_le_div_iff₀ (hden hx.1) (hden hy.1)).2
      rw [mul_add, mul_add, mul_one, mul_one, mul_comm (K * x) (K * y)]
      exact add_le_add (mul_le_mul_of_nonneg_left hxy hK) le_rfl
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfrac hqMax.le) hm
  have hstrict : StrictAntiOn (fun x => V * (c₀ - x) - m * q x) (Set.Icc 0 c₀) := by
    intro x hx y hy hxy
    have hL := mul_lt_mul_of_pos_left (sub_lt_sub_left hxy c₀) hV
    exact (sub_lt_sub_right hL (m * q y)).trans_le (sub_le_sub_left (hR_mono hx hy hxy.le) _)
  refine ⟨c, hc, hbalance, ?_, ?_, ?_⟩
  · intro d hd hroot
    apply hstrict.injOn hd hc
    simp only [hroot, hbalance, sub_self]
  · change qMax * (K * c / (1 + K * c)) / qMax ∈ Set.Ico 0 1
    rw [mul_comm qMax, mul_div_cancel_right₀ _ hqMax.ne']
    exact ⟨div_nonneg (mul_nonneg hK hc.1) (hden hc.1).le,
      (div_lt_one (hden hc.1)).2 (lt_add_of_pos_left _ zero_lt_one)⟩
  · intro hdegenerate
    have hzero : m * q c = 0 := by
      rcases hdegenerate with h | h
      · simp [q, h]
      · simp [h]
    have hdiff : c₀ - c = 0 := (mul_eq_zero.mp (hbalance.trans hzero)).resolve_left hV.ne'
    exact ⟨(sub_eq_zero.mp hdiff).symm, hzero⟩

end Chemistry.Separations
