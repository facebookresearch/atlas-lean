/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Basic
public import PhyslibExt.Chemistry.Calibration

/-!
# Inverse calibration error budget

## i. Overview

Error transfer for inverse prediction in a linear calibration
`y = a * x + b + e`, using the existing intercept-first
`Chemistry.Calibration.inversePrediction`. With perturbed
intercept and slope (`|da| ≤ Da`, `|db| ≤ Db`, `Da < |a|`), input
bounded by `|x| ≤ X` and residual bounded by `|e| ≤ E`, the
recovered input satisfies
`|xhat - x| ≤ (Da * X + Db + E) / (|a| - Da)`. The known-parameter
case is `E / |a|`. A measure form bounds the probability of the
bad event `{ω | B < |xhat ω - x ω|}` by the mass of the complement
of any good set on which the deterministic bound holds. No
distributional assumption on the residual is made.

## ii. Key results

- `inversePrediction_error_le`: the perturbed-parameter error
  bound.
- `inversePrediction_error_le_known_params`: the exact-parameter
  specialization `E / |a|`.
- `inversePrediction_error_bad_event_measure_le`: the bad-event
  measure bound.

## iii. Table of contents

- A. Inverse calibration budget

## iv. References

- JCGM 100:2008, *Guide to the Expression of Uncertainty in
  Measurement*: propagation of uncertainty through a measurement
  function, here the inverse calibration line.

## A. Inverse calibration budget

Discharges ECE roadmap leaf `ECE.SEN.CALIBRATION.L1` (sensor
calibration error budget).
-/

@[expose] public section

open Chemistry.Calibration

namespace PhyslibExt.Instrumentation.InverseCalibrationBudget

/-- Bounded-parameter-error transfer for inverse prediction. With true slope
`a`, true intercept `b`, perturbations `da`, `db`, observation error `e`,
observation `y = a * x + b + e`, and bounds `|x| <= X`, `|da| <= Da < |a|`,
`|db| <= Db`, `|e| <= E` (all bound constants nonnegative), the perturbed
inverse prediction `inversePrediction (b + db) (a + da) y` differs from `x`
by at most `(Da * X + Db + E) / (|a| - Da)`. -/
lemma inversePrediction_error_le (a b x X da Da db Db e E y : ℝ)
    (hX0 : 0 ≤ X) (hDa0 : 0 ≤ Da) (hDb0 : 0 ≤ Db) (hE0 : 0 ≤ E)
    (hDa : Da < |a|) (hx : |x| ≤ X) (hda : |da| ≤ Da) (hdb : |db| ≤ Db)
    (he : |e| ≤ E) (hy : y = a * x + b + e) :
    |inversePrediction (b + db) (a + da) y - x| ≤
      (Da * X + Db + E) / (|a| - Da) := by
  have hne : a + da ≠ 0 := by
    intro hcon
    have ha : a = -da := by linarith
    have habs : |a| = |da| := by rw [ha, abs_neg]
    linarith
  have hsub : inversePrediction (b + db) (a + da) y - x
      = (e - db - x * da) / (a + da) := by
    unfold inversePrediction
    rw [hy]
    field_simp
    ring
  have htri : |e - db - x * da| ≤ |e| + |db| + |x| * |da| := by
    have h1 : |e - db - x * da| ≤ |e - db| + |x * da| := abs_sub _ _
    have h2 : |e - db| ≤ |e| + |db| := abs_sub _ _
    rw [abs_mul] at h1
    linarith
  have hprod : |x| * |da| ≤ X * Da := mul_le_mul hx hda (abs_nonneg da) hX0
  have hnum : |e - db - x * da| ≤ Da * X + Db + E := by
    calc |e - db - x * da| ≤ |e| + |db| + |x| * |da| := htri
      _ ≤ E + Db + X * Da := add_le_add (add_le_add he hdb) hprod
      _ = Da * X + Db + E := by ring
  have hden : |a| - Da ≤ |a + da| := by
    have h2 : |(a + da) - da| ≤ |a + da| + |da| := abs_sub _ _
    have h3 : (a + da) - da = a := by ring
    rw [h3] at h2
    linarith
  have hDpos : 0 < |a| - Da := by linarith
  have hapos : 0 < |a + da| := by linarith
  have hNUM0 : 0 ≤ Da * X + Db + E := by
    have h1 : 0 ≤ Da * X := mul_nonneg hDa0 hX0
    linarith
  have hdiv1 : |e - db - x * da| / |a + da|
      ≤ (Da * X + Db + E) / |a + da| := by
    have hpos : (0 : ℝ) ≤ |a + da|⁻¹ := le_of_lt (inv_pos.mpr hapos)
    have h := mul_le_mul_of_nonneg_right hnum hpos
    simpa only [div_eq_mul_inv] using h
  have hdiv2 : (Da * X + Db + E) / |a + da|
      ≤ (Da * X + Db + E) / (|a| - Da) :=
    div_le_div_of_nonneg_left hNUM0 hDpos hden
  rw [hsub, abs_div]
  exact le_trans hdiv1 hdiv2

/-- Known-calibration reduction: with exact parameters (`da = db = 0`), the
bound of `inversePrediction_error_le` reduces to `E / |a|`. -/
lemma inversePrediction_error_le_known_params (a b x e E y : ℝ)
    (ha : a ≠ 0) (hE0 : 0 ≤ E) (he : |e| ≤ E) (hy : y = a * x + b + e) :
    |inversePrediction b a y - x| ≤ E / |a| := by
  have h := inversePrediction_error_le a b x |x| 0 0 0 0 e E y
    (abs_nonneg x) le_rfl le_rfl hE0 (abs_pos.mpr ha) le_rfl (by simp) (by simp)
    he hy
  simpa using h

/-- Event-level transfer by measure monotonicity only: if the pointwise
bound `|xhat ω - x ω| <= B` holds at every outcome of a set `Good`, then the
bad event where the bound fails has measure at most `μ Goodᶜ`, and hence at
most any `p` with `μ Goodᶜ <= p`. No distributional assumption is made. -/
lemma inversePrediction_error_bad_event_measure_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (xhat x : Ω → ℝ)
    (B p : ℝ) (Good : Set Ω)
    (hGood : ∀ ω ∈ Good, |xhat ω - x ω| ≤ B)
    (hp : μ Goodᶜ ≤ ENNReal.ofReal p) :
    μ {ω | B < |xhat ω - x ω|} ≤ ENNReal.ofReal p := by
  have hsub : {ω | B < |xhat ω - x ω|} ⊆ Goodᶜ := by
    intro ω hω
    rw [Set.mem_ofPred_eq] at hω
    rw [Set.mem_compl_iff]
    intro hmem
    have hle := hGood ω hmem
    linarith
  exact le_trans (MeasureTheory.measure_mono hsub) hp

end PhyslibExt.Instrumentation.InverseCalibrationBudget
