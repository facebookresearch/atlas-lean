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
`y = b * x + a + e`, using the existing intercept-first
`Chemistry.Calibration.inversePrediction` (intercept `a`, slope
`b`). With intercept perturbation `|da| ≤ Da` and slope
perturbation `|db| ≤ Db < |b|`, input bounded by `|x| ≤ X` and
residual bounded by `|e| ≤ E`, the recovered input satisfies
`|xhat - x| ≤ (Db * X + Da + E) / (|b| - Db)`. The known-parameter
case is `E / |b|`. A measure form bounds the probability of the
bad event `{ω | E / |b| < |xhat ω - x ω|}` by the probability of
the residual bad event `{ω | E < |e ω|}`, with no distributional
assumption on the residual.

## ii. Key results

- `inversePrediction_error_le`: the perturbed-parameter error
  bound.
- `inversePrediction_error_le_known_params`: the exact-parameter
  specialization `E / |b|`.
- `inversePrediction_error_event_measure_le`: the bad-event
  measure bound, composed from the deterministic bound on the
  good event.

## iii. Table of contents

- A. Inverse calibration budget

## iv. References

- JCGM 100:2008, *Guide to the Expression of Uncertainty in
  Measurement*: propagation of uncertainty through a measurement
  function, here the inverse calibration line.

## A. Inverse calibration budget
-/

@[expose] public section

open Chemistry.Calibration

namespace PhyslibExt.Instrumentation.InverseCalibrationBudget

/-- Bounded-parameter-error transfer for inverse prediction, in the
canonical intercept-first order of `inversePrediction`. With true
intercept `a`, true slope `b`, intercept perturbation `da` bounded by
`Da`, slope perturbation `db` bounded by `Db < |b|`, observation error
`e`, observation `y = b * x + a + e`, and bounds `|x| <= X`,
`|e| <= E` (all bound constants nonnegative), the perturbed inverse
prediction `inversePrediction (a + da) (b + db) y` differs from `x`
by at most `(Db * X + Da + E) / (|b| - Db)`. -/
lemma inversePrediction_error_le (a b x X da Da db Db e E y : ℝ)
    (hX0 : 0 ≤ X) (hDa0 : 0 ≤ Da) (hDb0 : 0 ≤ Db) (hE0 : 0 ≤ E)
    (hDb : Db < |b|) (hx : |x| ≤ X) (hda : |da| ≤ Da) (hdb : |db| ≤ Db)
    (he : |e| ≤ E) (hy : y = b * x + a + e) :
    |inversePrediction (a + da) (b + db) y - x| ≤
      (Db * X + Da + E) / (|b| - Db) := by
  have hne : b + db ≠ 0 := by
    intro hcon
    have hb : b = -db := by linarith
    have habs : |b| = |db| := by rw [hb, abs_neg]
    linarith
  have hsub : inversePrediction (a + da) (b + db) y - x
      = (e - da - x * db) / (b + db) := by
    unfold inversePrediction
    rw [hy]
    field_simp
    ring
  have htri : |e - da - x * db| ≤ |e| + |da| + |x| * |db| := by
    have h1 : |e - da - x * db| ≤ |e - da| + |x * db| := abs_sub _ _
    have h2 : |e - da| ≤ |e| + |da| := abs_sub _ _
    rw [abs_mul] at h1
    linarith
  have hprod : |x| * |db| ≤ X * Db := mul_le_mul hx hdb (abs_nonneg db) hX0
  have hnum : |e - da - x * db| ≤ Db * X + Da + E := by
    calc |e - da - x * db| ≤ |e| + |da| + |x| * |db| := htri
      _ ≤ E + Da + X * Db := add_le_add (add_le_add he hda) hprod
      _ = Db * X + Da + E := by ring
  have hden : |b| - Db ≤ |b + db| := by
    have h2 : |(b + db) - db| ≤ |b + db| + |db| := abs_sub _ _
    have h3 : (b + db) - db = b := by ring
    rw [h3] at h2
    linarith
  have hDpos : 0 < |b| - Db := by linarith
  have hapos : 0 < |b + db| := by linarith
  have hNUM0 : 0 ≤ Db * X + Da + E := by
    have h1 : 0 ≤ Db * X := mul_nonneg hDb0 hX0
    linarith
  have hdiv1 : |e - da - x * db| / |b + db|
      ≤ (Db * X + Da + E) / |b + db| := by
    have hpos : (0 : ℝ) ≤ |b + db|⁻¹ := le_of_lt (inv_pos.mpr hapos)
    have h := mul_le_mul_of_nonneg_right hnum hpos
    simpa only [div_eq_mul_inv] using h
  have hdiv2 : (Db * X + Da + E) / |b + db|
      ≤ (Db * X + Da + E) / (|b| - Db) :=
    div_le_div_of_nonneg_left hNUM0 hDpos hden
  rw [hsub, abs_div]
  exact le_trans hdiv1 hdiv2

/-- Known-calibration reduction: with exact parameters (`da = db = 0`), the
bound of `inversePrediction_error_le` reduces to `E / |b|`. -/
lemma inversePrediction_error_le_known_params (a b x e E y : ℝ)
    (hb : b ≠ 0) (hE0 : 0 ≤ E) (he : |e| ≤ E) (hy : y = b * x + a + e) :
    |inversePrediction a b y - x| ≤ E / |b| := by
  have h := inversePrediction_error_le a b x |x| 0 0 0 0 e E y
    (abs_nonneg x) le_rfl le_rfl hE0 (abs_pos.mpr hb) le_rfl (by simp) (by simp)
    he hy
  simpa using h

/-- Event-level transfer by measure monotonicity only: if the pointwise
bound `|xhat ω - x ω| <= B` holds at every outcome of a set `Good`, then the
bad event where the bound fails has measure at most `μ Goodᶜ`, and hence at
most any `p` with `μ Goodᶜ <= p`. No distributional assumption is made. -/
private lemma inversePrediction_error_bad_event_measure_le {Ω : Type*}
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

/-- Calibration bad-event bound, derived from the deterministic
known-parameter bound: on the good event that the residual obeys
`|e ω| ≤ E`, the recovered input `inversePrediction a b (y ω)` with
`y ω = b * x ω + a + e ω` differs from `x ω` by at most `E / |b|`,
so the bad event is contained in the residual bad event. -/
lemma inversePrediction_error_event_measure_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (a b E p : ℝ) (hb : b ≠ 0) (hE : 0 ≤ E) (x e : Ω → ℝ)
    (hp : μ {ω | E < |e ω|} ≤ ENNReal.ofReal p) :
    μ {ω | E / |b| <
      |inversePrediction a b (b * x ω + a + e ω) - x ω|}
      ≤ ENNReal.ofReal p := by
  refine inversePrediction_error_bad_event_measure_le μ
    (fun ω => inversePrediction a b (b * x ω + a + e ω)) x (E / |b|) p
    {ω | |e ω| ≤ E} ?_ ?_
  · intro ω hω
    rw [Set.mem_ofPred_eq] at hω
    exact inversePrediction_error_le_known_params a b (x ω) (e ω) E
      (b * x ω + a + e ω) hb hE hω rfl
  · have hset : {ω | |e ω| ≤ E}ᶜ = {ω | E < |e ω|} := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    rw [hset]
    exact hp

end PhyslibExt.Instrumentation.InverseCalibrationBudget
