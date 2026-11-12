/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Independence.Basic

/-!
# Flood frequency: probability of no exceedance in `n` years

If yearly no-exceedance events are independent with common probability
`1 - p`, the probability of no exceedance in `n` years is `(1 - p) ^ n`.

## i. Overview

Independence turns the measure of the intersection into the product of
the measures (`iIndepSet_iff_meas_biInter`); with common probability
`1 - p` the product is `(1 - p) ^ n`. This is a statement about a
probability measure, not a schedule, and it makes no empirical
stationarity claim: serial dependence breaks it, and a changed climate
distribution is not stationary. The return-period convention `1 / p`
is stated for `p > 0`.

## ii. Key results

- `EarthScience.no_exceedance_prob`: no exceedance in `n` years has
  probability `(1 - p) ^ n`.

## iii. Table of contents

- A. No exceedance in `n` years

## iv. References

- `ProbabilityTheory.iIndepSet_iff_meas_biInter` (Mathlib).

## A. No exceedance in `n` years
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace EarthScience

/-- No exceedance in `n` years: if the yearly no-exceedance events `F i`
are independent and each has probability `1 - p`, then the probability
of no exceedance in any of the `n` years is `(1 - p) ^ n`. -/
theorem no_exceedance_prob {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {p : ℝ}
    {F : Fin n → Set Ω} (hp : 0 ≤ p ∧ p ≤ 1) (hMeas : ∀ i, MeasurableSet (F i))
    (hIndep : iIndepSet F μ) (hProb : ∀ i, (μ (F i)).toReal = 1 - p) :
    (μ (⋂ i, F i)).toReal = (1 - p) ^ n := by
  have _ := hp
  have h := ((iIndepSet_iff_meas_biInter hMeas).mp hIndep) Finset.univ
  have hInter : (⋂ i ∈ (Finset.univ : Finset (Fin n)), F i) = (⋂ i, F i) := by simp
  rw [hInter] at h
  have hToReal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_prod] at hToReal
  simp only [hProb] at hToReal
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hToReal
  exact hToReal

end EarthScience
