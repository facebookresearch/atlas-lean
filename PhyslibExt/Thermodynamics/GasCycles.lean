/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gas cycles: refrigeration and power cycles

## i. Overview

Engineering cycle results, one section per device. Each cycle runs between reservoirs at
absolute temperatures (`T > 0`); heats and works are per cycle, and the first law over the cycle
(`ΔU = 0`) relates them. The second law enters only as the Clausius inequality, a model input
stated as a hypothesis, as in `PhyslibExt.Chemistry.Thermodynamics.Entropy`.

Refrigerators and heat pumps (section A). A cycle absorbs `Qc` from a cold reservoir at `Tc`,
rejects `Qh` to a hot one at `Th` (`0 < Tc < Th`) and takes the work input `W = Qh - Qc`, the
work done on the working fluid (the engineering `W_out` of `PhyslibExt.Thermodynamics.ProcessPorts`
is `-W`). The refrigerator Clausius inequality reads `0 ≤ Qh / Th - Qc / Tc`. The coefficients of
performance `COP_R = Qc / W` and `COP_HP = Qh / W` are ratios of heat to work, not heat-engine
efficiencies, and can exceed one. With `W > 0` the Clausius inequality bounds them by the
reversible values `Tc / (Th - Tc)` and `Th / (Th - Tc)`, with equality exactly at zero Clausius
residual. Pumping heat `Qc > 0` uphill forces `W > 0`, and at `Th = Tc` no finite bound exists.

## ii. Key results

- `GasCycles.work_pos_of_clausius`: pumping heat `Qc > 0` uphill needs `W > 0`.
- `GasCycles.cop_le_carnot`: `Qc / W ≤ Tc / (Th - Tc)` and `Qh / W ≤ Th / (Th - Tc)`.
- `GasCycles.cop_eq_carnot_iff`: equality exactly at zero Clausius residual.
- `GasCycles.cop_unbounded_of_eq`: equal reservoir temperatures admit no finite bound.

## iii. Table of contents

- A. Coefficients of performance and their second-law bounds

## iv. References

- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 6:
  `COP_R = Q_L / W_net,in`, `COP_HP = Q_H / W_net,in`, the reversible values
  `1 / (T_H / T_L - 1)` and `1 / (1 - T_L / T_H)`, and the Clausius statement.
- MIT OpenCourseWare, 5.60 *Thermodynamics & Kinetics* (Spring 2008): the Clausius inequality.
-/

@[expose] public section

namespace GasCycles

/-! ## A. Coefficients of performance and their second-law bounds -/

/-- Pumping heat uphill needs work (the Clausius statement): between reservoirs at
`0 < Tc < Th`, a cycle that absorbs `Qc > 0` at `Tc`, rejects `Qh` at `Th` and satisfies the
refrigerator Clausius inequality `0 ≤ Qh / Th - Qc / Tc` has work input `W = Qh - Qc > 0`. -/
lemma work_pos_of_clausius {Qh Qc W Tc Th : ℝ} (hTc : 0 < Tc) (hT : Tc < Th) (hQc : 0 < Qc)
    (hW : W = Qh - Qc) (hClausius : 0 ≤ Qh / Th - Qc / Tc) :
    0 < W := by
  have hTh : 0 < Th := lt_trans hTc hT
  have h1 : Qc / Tc ≤ Qh / Th := by linarith
  have h2 : Qc * Th ≤ Qh * Tc := (div_le_div_iff₀ hTc hTh).mp h1
  have h3 : Qc * Tc < Qc * Th := mul_lt_mul_of_pos_left hT hQc
  have h4 : Qc * Tc < Qh * Tc := lt_of_lt_of_le h3 h2
  have h5 : Qc < Qh := by
    by_contra hcon
    have hle : Qh ≤ Qc := le_of_not_gt hcon
    have h6 : Qh * Tc ≤ Qc * Tc := mul_le_mul_of_nonneg_right hle (le_of_lt hTc)
    linarith
  linarith

/-- Second-law bounds on the coefficients of performance: between reservoirs at `0 < Tc < Th`,
with work input `W = Qh - Qc > 0` and the refrigerator Clausius inequality
`0 ≤ Qh / Th - Qc / Tc`, the refrigerator `COP_R = Qc / W` is at most `Tc / (Th - Tc)` and the
heat pump `COP_HP = Qh / W` is at most `Th / (Th - Tc)`. -/
lemma cop_le_carnot {Qh Qc W Tc Th : ℝ} (hTc : 0 < Tc) (hT : Tc < Th) (hW : W = Qh - Qc)
    (hWpos : 0 < W) (hClausius : 0 ≤ Qh / Th - Qc / Tc) :
    Qc / W ≤ Tc / (Th - Tc) ∧ Qh / W ≤ Th / (Th - Tc) := by
  have hTh : 0 < Th := lt_trans hTc hT
  have hD : 0 < Th - Tc := sub_pos.mpr hT
  have h2 : Qc * Th ≤ Qh * Tc := (div_le_div_iff₀ hTc hTh).mp (by linarith)
  constructor
  · rw [div_le_div_iff₀ hWpos hD, hW]
    linarith
  · rw [div_le_div_iff₀ hWpos hD, hW]
    linarith

/-- Equality exactly at zero Clausius residual: with `0 < Tc < Th` and `W = Qh - Qc > 0`,
`COP_R = Tc / (Th - Tc)` holds if and only if `Qh / Th - Qc / Tc = 0`, and likewise
`COP_HP = Th / (Th - Tc)`. The Clausius inequality is not needed for the equivalence. -/
lemma cop_eq_carnot_iff {Qh Qc W Tc Th : ℝ} (hTc : 0 < Tc) (hT : Tc < Th) (hW : W = Qh - Qc)
    (hWpos : 0 < W) :
    (Qc / W = Tc / (Th - Tc) ↔ Qh / Th - Qc / Tc = 0) ∧
      (Qh / W = Th / (Th - Tc) ↔ Qh / Th - Qc / Tc = 0) := by
  have hTh : 0 < Th := lt_trans hTc hT
  have hD : 0 < Th - Tc := sub_pos.mpr hT
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hDne : Th - Tc ≠ 0 := ne_of_gt hD
  have hTcne : Tc ≠ 0 := ne_of_gt hTc
  have hThne : Th ≠ 0 := ne_of_gt hTh
  have hres : Qh / Th - Qc / Tc = 0 ↔ Qc * Th = Qh * Tc := by
    rw [sub_eq_zero, div_eq_div_iff hThne hTcne]
    exact eq_comm
  constructor
  · rw [div_eq_div_iff hWne hDne, hW, hres]
    constructor <;> intro h <;> linarith
  · rw [div_eq_div_iff hWne hDne, hW, hres]
    constructor <;> intro h <;> linarith

/-- Equal reservoir temperatures admit no finite bound: at `Th = Tc = T > 0`, for every `M`
there are heats and work with `Qc > 0`, `W = Qh - Qc > 0` and the Clausius inequality whose
`COP_R` and `COP_HP` both exceed `M`. The hypothesis `Tc < Th` of `cop_le_carnot` cannot be
weakened to `Tc ≤ Th`. -/
lemma cop_unbounded_of_eq {T : ℝ} (hT : 0 < T) (M : ℝ) :
    ∃ Qh Qc W : ℝ, 0 < Qc ∧ W = Qh - Qc ∧ 0 < W ∧ 0 ≤ Qh / T - Qc / T ∧
      M < Qc / W ∧ M < Qh / W := by
  refine ⟨|M| + 2, |M| + 1, 1, by positivity, by ring, by norm_num, ?_, ?_, ?_⟩
  · have h : (|M| + 2) / T - (|M| + 1) / T = 1 / T := by
      rw [← sub_div]
      congr 1
      ring
    rw [h]
    exact le_of_lt (div_pos one_pos hT)
  · rw [div_one]
    have hM := le_abs_self M
    linarith
  · rw [div_one]
    have hM := le_abs_self M
    linarith

end GasCycles
