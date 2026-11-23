/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp

/-!
# Flood frequency: exceedance probabilities in `n` years

If yearly no-exceedance events are independent with common probability
`1 - p`, the probability of no exceedance in `n` years is `(1 - p) ^ n`,
so the probability of at least one exceedance is `1 - (1 - p) ^ n`.

## i. Overview

Independence turns the measure of the intersection into the product of
the measures (`iIndepSet_iff_meas_biInter`); with common probability
`1 - p` the product is `(1 - p) ^ n`. This is a statement about a
probability measure, not a schedule, and it makes no empirical
stationarity claim: serial dependence breaks it, and a changed climate
distribution is not stationary. The at-least-one form is the complement
of the no-exceedance event. This module provides these horizon
probabilities, not a return-period API; the reciprocal display only
uses `T = 1 / p` for `p > 0`, with `T` measured in years.

## ii. Key results

- `EarthScience.no_exceedance_prob`: no exceedance in `n` years has
  probability `(1 - p) ^ n`.
- `EarthScience.at_least_one_exceedance_prob`: at least one
  exceedance in `n` years has probability `1 - (1 - p) ^ n`.
- `EarthScience.at_least_one_exceedance_prob_inv`: the same
  probability displayed with `T = 1 / p` for `p > 0`.

## iii. Table of contents

- A. Exceedance probabilities in `n` years

## iv. References

- `ProbabilityTheory.iIndepSet_iff_meas_biInter` (Mathlib).

## A. Exceedance probabilities in `n` years
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

/-- At-least-one exceedance from a supplied no-exceedance
probability. If `F i` is the no-exceedance event in year `i`
and the probability of no exceedance in any of the `n` years
is `(1 - p) ^ n`, then the probability of an exceedance in at
least one year is `1 - (1 - p) ^ n`. -/
lemma at_least_one_exceedance_prob_of_no_exceedance
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {p : ℝ}
    {F : Fin n → Set Ω} (hMeas : ∀ i, MeasurableSet (F i))
    (hno : (μ (⋂ i, F i)).toReal = (1 - p) ^ n) :
    (μ (⋃ i, (F i)ᶜ)).toReal = 1 - (1 - p) ^ n := by
  have hI : MeasurableSet (⋂ i, F i) := MeasurableSet.iInter hMeas
  rw [← Set.compl_iInter, prob_compl_eq_one_sub hI,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  simp [hno]

/-- Reciprocal form of the at-least-one exceedance
probability: when `0 < p` and `T = 1 / p`, the same supplied
no-exceedance probability gives
`1 - (1 - 1 / T) ^ n`. This uses `T` only as the displayed
reciprocal; it defines no return-period API. -/
lemma at_least_one_exceedance_prob_of_no_exceedance_inv
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {p T : ℝ}
    {F : Fin n → Set Ω} (hp : 0 < p) (hT : T = 1 / p)
    (hMeas : ∀ i, MeasurableSet (F i))
    (hno : (μ (⋂ i, F i)).toReal = (1 - p) ^ n) :
    (μ (⋃ i, (F i)ᶜ)).toReal = 1 - (1 - 1 / T) ^ n := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  rw [at_least_one_exceedance_prob_of_no_exceedance hMeas hno, hT]
  field_simp

/-- At least one exceedance in `n` years: if `p` is the annual
exceedance probability in `[0, 1]`, the yearly no-exceedance
events `F i` are independent, and each has probability `1 - p`,
then the probability of an exceedance in at least one of the
`n` years is `1 - (1 - p) ^ n`. Independence and the constant
annual probability are assumptions of the model, supplied here
through `no_exceedance_prob`. -/
theorem at_least_one_exceedance_prob {Ω : Type*}
    {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {p : ℝ}
    {F : Fin n → Set Ω} (hp : 0 ≤ p ∧ p ≤ 1)
    (hMeas : ∀ i, MeasurableSet (F i))
    (hIndep : iIndepSet F μ)
    (hProb : ∀ i, (μ (F i)).toReal = 1 - p) :
    (μ (⋃ i, (F i)ᶜ)).toReal = 1 - (1 - p) ^ n :=
  at_least_one_exceedance_prob_of_no_exceedance hMeas
    (no_exceedance_prob hp hMeas hIndep hProb)

/-- At least one exceedance in `n` years, displayed with the
reciprocal `T = 1 / p` for an annual exceedance probability
`p` with `0 < p ≤ 1`; `T` is measured in years. Under the same
independence and constant-probability assumptions as
`at_least_one_exceedance_prob`, the probability is
`1 - (1 - 1 / T) ^ n`. This display defines no return-period
API. -/
theorem at_least_one_exceedance_prob_inv {Ω : Type*}
    {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {p T : ℝ}
    {F : Fin n → Set Ω} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hT : T = 1 / p) (hMeas : ∀ i, MeasurableSet (F i))
    (hIndep : iIndepSet F μ)
    (hProb : ∀ i, (μ (F i)).toReal = 1 - p) :
    (μ (⋃ i, (F i)ᶜ)).toReal = 1 - (1 - 1 / T) ^ n :=
  at_least_one_exceedance_prob_of_no_exceedance_inv hp0 hT hMeas
    (no_exceedance_prob ⟨hp0.le, hp1⟩ hMeas hIndep hProb)

end EarthScience
