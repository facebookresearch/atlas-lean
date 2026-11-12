/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.H10FloodFrequency

/-!
# Flood-frequency checks

Concrete consumers of `PhyslibExt.EarthScience.H10FloodFrequency`:
the `n = 1` case, the `100`-year flood (`p = 0.01`) over 100 years,
and the `p = 0` / `p = 1` boundaries.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. `n = 1` and the 100-year flood
- B. Boundaries

## iv. References

- `PhyslibExt.EarthScience.H10FloodFrequency`
-/

open MeasureTheory ProbabilityTheory

/-- `n = 1`: no exceedance in one year has probability `1 - p`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p : ℝ} {F : Fin 1 → Set Ω}
    (hp : 0 ≤ p ∧ p ≤ 1) (hMeas : ∀ i, MeasurableSet (F i))
    (hIndep : iIndepSet F μ) (hProb : ∀ i, (μ (F i)).toReal = 1 - p) :
    (μ (⋂ i, F i)).toReal = (1 - p) ^ 1 :=
  EarthScience.no_exceedance_prob hp hMeas hIndep hProb

/-- A `100`-year flood (`p = 0.01`) has no-exceedance probability
`(0.99) ^ 100` over 100 years. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F : Fin 100 → Set Ω}
    (hMeas : ∀ i, MeasurableSet (F i))
    (hIndep : iIndepSet F μ) (hProb : ∀ i, (μ (F i)).toReal = 1 - (0.01 : ℝ)) :
    (μ (⋂ i, F i)).toReal = (1 - (0.01 : ℝ)) ^ 100 :=
  EarthScience.no_exceedance_prob (by norm_num) hMeas hIndep hProb

/-- Boundaries: `p = 0` gives `1`, `p = 1` with `n = 3` gives `0`. -/
example : (1 - 0 : ℝ) ^ 5 = 1 := by
  simp

/-- `p = 1` with `n = 3` gives no-exceedance probability `0`. -/
example : 0 < 3 → (1 - 1 : ℝ) ^ 3 = 0 := by
  intro hn
  simpa only [sub_self] using (zero_pow (ne_of_gt hn) : (0 : ℝ) ^ 3 = 0)

/-- Return period: `p = 0.01` gives `(1 / 0.01) * 0.01 = 1`. -/
example : (0 : ℝ) < 0.01 → ((1 : ℝ) / 0.01) * 0.01 = 1 := by
  intro hp
  exact div_mul_cancel₀ 1 (ne_of_gt hp)
