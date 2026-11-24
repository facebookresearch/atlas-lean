/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import PhyslibExt.Electronics.LogicObservationBands
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Synchronizer observation budget

## i. Overview

A family of clock-domain-crossing observations is indexed by a
finite type. Each observation has a resolution time and a settling
budget, both supplied per index as data. The module does not model
how a budget arises from clock periods or timing margins, and the
index ranges over observations rather than synchronizer stages, so
it is an abstract union-bound adapter: a synchronizer analysis
supplies the budgets, the settling guarantee and the tail bounds,
and the results here combine them. The supplied settling guarantee
states that, once an observation has resolved within its budget,
its ideal voltage encodes its expected bit in the usual low or
high output band and its additive noise is below both noise
margins, the minimum of `Vil - Vol` and `Voh - Vih`. The observed
voltage is the ideal voltage plus that noise, so the within-budget
step is the canonical noise-preservation result
`LogicObservationBands.observe_noisy_output` applied to that sum.
Hence an invalid observation, one whose voltage lies strictly
between the input thresholds `Vil` and `Vih` and whose
three-valued observation is `none`, can occur only after its
budget has expired. That inclusion is proved by contraposition
from the within-budget observation. If each budget-expiry event
has an exponential tail bound `c * exp (-budget_i / tau)` in the
extended nonnegative reals, the finite union bound, with no
independence assumption, bounds the probability of any invalid
observation by `min (1, sum_i c * exp (-budget_i / tau))`; equal
budgets give `min (1, N * c * exp (-b / tau))`, where `N` is the
number of observations. The tail bound is a hypothesis throughout,
not a consequence of a device model, and no finite deterministic
resolution deadline is inferred from it.

## ii. Key results

- `observe_observedVoltage_eq_some_of_le` and
  `not_invalidObservation_of_le`: within budget, the observed
  voltage is observed as the expected bit and is not invalid.
- `resolutionExceeds_of_invalidObservation` and
  `invalidEvent_subset_resolutionExceedsEvent`: an invalid
  observation implies that its resolution time exceeds its
  budget, in pointwise and event form.
- `measure_invalidEvent_le_of_tail`: the per-index exponential
  tail bound transfers from the budget-expiry event to the
  invalid event by monotonicity of measure.
- `measure_biUnion_invalidEvent_le_sum`,
  `anyInvalid_measure_le_min_one_sum` and
  `measure_biUnion_invalidEvent_le_min_one_card_mul`: the finite
  union bound, the headline bound capped at the total probability
  `1`, and the equal-budget form.

## iii. Table of contents

- A. Observation events and the settling guarantee
- B. Within-budget observation
- C. Invalid observations and budget expiry
- D. Tail bounds and the finite union bound
- E. Validation cases

## iv. References

- W. J. Dally and J. W. Poulton, *Digital Systems Engineering*,
  Cambridge University Press, 1998: synchronizers for signals
  crossing between clock domains, metastability, and the
  exponential decrease of synchronizer failure probability with
  the time allowed for resolution.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PhyslibExt.Electronics.SynchronizerObservationBudget

open PhyslibExt.Electronics.LogicObservationBands

/-! ## A. Observation events and the settling guarantee -/

/-- An observation is invalid when its voltage falls in the invalid
band between the thresholds, so the three-valued observation is
`none`. -/
def invalidObservation (Vil Vih v : ℝ) : Prop :=
  observe Vil Vih v = none

/-- The supplied analog settling model. The observed voltage is the
ideal voltage plus additive noise. Whenever the resolution time is
within the budget, the ideal voltage encodes the expected bit in its
output band (`Vol` on the low side, `Voh` on the high side) and the
noise is below both noise margins formed from `Vol < Vil` and
`Vih < Voh`. No claim is made outside the stated budget. -/
def settlingGuarantee {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}
    (Vil Vih Vol Voh : ℝ) (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool) : Prop :=
  (∀ (i : ι) (ω : Ω), observedVoltage i ω = idealVoltage i ω + noise i ω) ∧
    (∀ (i : ι) (ω : Ω), resolutionTime i ω ≤ budget i →
      (expectedBit i ω = false ∧ idealVoltage i ω ≤ Vol) ∨
        (expectedBit i ω = true ∧ Voh ≤ idealVoltage i ω)) ∧
    (∀ (i : ι) (ω : Ω), resolutionTime i ω ≤ budget i →
      |noise i ω| < min (Vil - Vol) (Voh - Vih))

/-- The invalid-observation event for one observation index. -/
def invalidEvent {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (Vil Vih : ℝ)
    (observedVoltage : ι → Ω → ℝ) (i : ι) : Set Ω :=
  {ω : Ω | invalidObservation Vil Vih (observedVoltage i ω)}

/-- The budget-expiry event for one observation index: the resolution
time exceeds its settling budget. -/
def resolutionExceedsEvent {Ω : Type*} {ι : Type*}
    (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ) (i : ι) : Set Ω :=
  {ω : Ω | budget i < resolutionTime i ω}

/-! ## B. Within-budget observation -/

/-- Within budget, under the settling model, the observed voltage is
observed as the expected bit. -/
lemma observe_observedVoltage_eq_some_of_le {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} (Vil Vih Vol Voh : ℝ) (hVol : Vol < Vil) (hVilVih : Vil < Vih)
    (hVoh : Vih < Voh) (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool)
    (hmodel : settlingGuarantee Vil Vih Vol Voh resolutionTime budget
      idealVoltage noise observedVoltage expectedBit)
    (i : ι) (ω : Ω) (hres : resolutionTime i ω ≤ budget i) :
    observe Vil Vih (observedVoltage i ω) = some (expectedBit i ω) := by
  obtain ⟨hobs, hband, hnoise⟩ := hmodel
  have h := observe_noisy_output hVol hVilVih hVoh (expectedBit i ω)
    (idealVoltage i ω) (noise i ω) (hband i ω hres) (hnoise i ω hres)
  rw [hobs i ω]
  exact h

/-- Within budget, under the settling model, the observation is not
invalid. -/
lemma not_invalidObservation_of_le {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} (Vil Vih Vol Voh : ℝ) (hVol : Vol < Vil) (hVilVih : Vil < Vih)
    (hVoh : Vih < Voh) (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool)
    (hmodel : settlingGuarantee Vil Vih Vol Voh resolutionTime budget
      idealVoltage noise observedVoltage expectedBit)
    (i : ι) (ω : Ω) (hres : resolutionTime i ω ≤ budget i) :
    ¬ invalidObservation Vil Vih (observedVoltage i ω) := by
  intro hcon
  have h := observe_observedVoltage_eq_some_of_le Vil Vih Vol Voh hVol hVilVih hVoh
    resolutionTime budget idealVoltage noise observedVoltage expectedBit hmodel i ω hres
  unfold invalidObservation at hcon
  rw [h] at hcon
  simp at hcon

/-! ## C. Invalid observations and budget expiry -/

/-- **Invalid implies unresolved.** Under the settling model, an
invalid observation can occur only after its settling budget has
expired: its resolution time strictly exceeds its budget. -/
lemma resolutionExceeds_of_invalidObservation {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} (Vil Vih Vol Voh : ℝ) (hVol : Vol < Vil) (hVilVih : Vil < Vih)
    (hVoh : Vih < Voh) (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool)
    (hmodel : settlingGuarantee Vil Vih Vol Voh resolutionTime budget
      idealVoltage noise observedVoltage expectedBit)
    (i : ι) (ω : Ω) (hinvalid : invalidObservation Vil Vih (observedVoltage i ω)) :
    budget i < resolutionTime i ω := by
  by_contra hcon
  have hle : resolutionTime i ω ≤ budget i := le_of_not_gt hcon
  exact (not_invalidObservation_of_le Vil Vih Vol Voh hVol hVilVih hVoh
    resolutionTime budget idealVoltage noise observedVoltage expectedBit hmodel i ω hle)
    hinvalid

/-- The invalid-observation event of each index is contained in its
budget-expiry event. -/
lemma invalidEvent_subset_resolutionExceedsEvent {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} (Vil Vih Vol Voh : ℝ) (hVol : Vol < Vil) (hVilVih : Vil < Vih)
    (hVoh : Vih < Voh) (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool)
    (hmodel : settlingGuarantee Vil Vih Vol Voh resolutionTime budget
      idealVoltage noise observedVoltage expectedBit) (i : ι) :
    invalidEvent Vil Vih observedVoltage i ⊆
      resolutionExceedsEvent resolutionTime budget i := by
  intro ω hmem
  exact resolutionExceeds_of_invalidObservation Vil Vih Vol Voh hVol hVilVih hVoh
    resolutionTime budget idealVoltage noise observedVoltage expectedBit hmodel i ω hmem

/-- Per-index tail bound for an invalid observation, from its
budget-expiry tail bound. -/
lemma measure_invalidEvent_le_of_tail {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} (μ : Measure Ω) [IsProbabilityMeasure μ] (Vil Vih Vol Voh : ℝ)
    (hVol : Vol < Vil) (hVilVih : Vil < Vih) (hVoh : Vih < Voh)
    (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool)
    (hmodel : settlingGuarantee Vil Vih Vol Voh resolutionTime budget
      idealVoltage noise observedVoltage expectedBit)
    (c tau : ℝ) (i : ι)
    (htail : μ (resolutionExceedsEvent resolutionTime budget i) ≤
      ENNReal.ofReal (c * Real.exp (-budget i / tau))) :
    μ (invalidEvent Vil Vih observedVoltage i) ≤
      ENNReal.ofReal (c * Real.exp (-budget i / tau)) := by
  calc μ (invalidEvent Vil Vih observedVoltage i)
      ≤ μ (resolutionExceedsEvent resolutionTime budget i) :=
        measure_mono (invalidEvent_subset_resolutionExceedsEvent Vil Vih Vol Voh hVol
          hVilVih hVoh resolutionTime budget idealVoltage noise observedVoltage expectedBit
          hmodel i)
    _ ≤ ENNReal.ofReal (c * Real.exp (-budget i / tau)) := htail

/-! ## D. Tail bounds and the finite union bound -/

/-- **Finite union bound, unequal budgets.** With measurable invalid
events and a per-index exponential tail bound, the probability of any
invalid observation is at most the sum of the tail bounds. No
independence is assumed. -/
lemma measure_biUnion_invalidEvent_le_sum {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vil Vih Vol Voh : ℝ) (hVol : Vol < Vil) (hVilVih : Vil < Vih)
    (hVoh : Vih < Voh) (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool)
    (hmodel : settlingGuarantee Vil Vih Vol Voh resolutionTime budget
      idealVoltage noise observedVoltage expectedBit)
    (hmeas : ∀ i : ι, MeasurableSet (invalidEvent Vil Vih observedVoltage i))
    (c tau : ℝ) (hc : 0 ≤ c) (htau : 0 < tau) (hb : ∀ i : ι, 0 ≤ budget i)
    (htail : ∀ i : ι, μ (resolutionExceedsEvent resolutionTime budget i) ≤
      ENNReal.ofReal (c * Real.exp (-budget i / tau))) :
    μ (⋃ i : ι, invalidEvent Vil Vih observedVoltage i) ≤
      ∑ i : ι, ENNReal.ofReal (c * Real.exp (-budget i / tau)) := by
  calc μ (⋃ i : ι, invalidEvent Vil Vih observedVoltage i)
      ≤ ∑' i : ι, μ (invalidEvent Vil Vih observedVoltage i) :=
        measure_iUnion_le _
    _ = ∑ i : ι, μ (invalidEvent Vil Vih observedVoltage i) := tsum_fintype _
    _ ≤ ∑ i : ι, ENNReal.ofReal (c * Real.exp (-budget i / tau)) := by
        apply Finset.sum_le_sum
        intro i _
        exact measure_invalidEvent_le_of_tail μ Vil Vih Vol Voh hVol hVilVih hVoh
          resolutionTime budget idealVoltage noise observedVoltage expectedBit hmodel c tau
          i (htail i)

/-- **Synchronizer observation budget.** The capped finite union bound
for any invalid observation, under the settling model and the
exponential resolution tail: the union bound capped at one, the total
probability of the space. This carries the pointwise
invalid-implies-unresolved inclusion and needs no independence. -/
lemma anyInvalid_measure_le_min_one_sum {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vil Vih Vol Voh : ℝ) (hVol : Vol < Vil) (hVilVih : Vil < Vih)
    (hVoh : Vih < Voh) (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool)
    (hmodel : settlingGuarantee Vil Vih Vol Voh resolutionTime budget
      idealVoltage noise observedVoltage expectedBit)
    (hmeas : ∀ i : ι, MeasurableSet (invalidEvent Vil Vih observedVoltage i))
    (c tau : ℝ) (hc : 0 ≤ c) (htau : 0 < tau) (hb : ∀ i : ι, 0 ≤ budget i)
    (htail : ∀ i : ι, μ (resolutionExceedsEvent resolutionTime budget i) ≤
      ENNReal.ofReal (c * Real.exp (-budget i / tau))) :
    μ (⋃ i : ι, invalidEvent Vil Vih observedVoltage i) ≤
      min 1 (∑ i : ι, ENNReal.ofReal (c * Real.exp (-budget i / tau))) := by
  refine le_min ?_ ?_
  · calc μ (⋃ i : ι, invalidEvent Vil Vih observedVoltage i)
        ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · exact measure_biUnion_invalidEvent_le_sum μ Vil Vih Vol Voh hVol hVilVih hVoh
      resolutionTime budget idealVoltage noise observedVoltage expectedBit hmodel hmeas c tau
      hc htau hb htail

/-- **Equal budgets.** When every budget equals one nonnegative budget
`b`, the capped union bound is `min (1, N * c * exp (-b / tau))`, with
`N` the number of observations and the product taken in the extended
nonnegative reals. -/
lemma measure_biUnion_invalidEvent_le_min_one_card_mul {Ω : Type*}
    [MeasurableSpace Ω] {ι : Type*} [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Vil Vih Vol Voh : ℝ) (hVol : Vol < Vil) (hVilVih : Vil < Vih)
    (hVoh : Vih < Voh) (resolutionTime : ι → Ω → ℝ) (budget : ι → ℝ)
    (idealVoltage : ι → Ω → ℝ) (noise : ι → Ω → ℝ)
    (observedVoltage : ι → Ω → ℝ) (expectedBit : ι → Ω → Bool)
    (hmodel : settlingGuarantee Vil Vih Vol Voh resolutionTime budget
      idealVoltage noise observedVoltage expectedBit)
    (hmeas : ∀ i : ι, MeasurableSet (invalidEvent Vil Vih observedVoltage i))
    (c tau b : ℝ) (hc : 0 ≤ c) (htau : 0 < tau) (hb : 0 ≤ b)
    (hbudget : ∀ i : ι, budget i = b)
    (htail : ∀ i : ι, μ (resolutionExceedsEvent resolutionTime budget i) ≤
      ENNReal.ofReal (c * Real.exp (-budget i / tau))) :
    μ (⋃ i : ι, invalidEvent Vil Vih observedVoltage i) ≤
      min 1 ((Fintype.card ι : ℝ≥0∞) *
        ENNReal.ofReal (c * Real.exp (-b / tau))) := by
  have hsum : ∑ i : ι, ENNReal.ofReal (c * Real.exp (-budget i / tau))
      = (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (c * Real.exp (-b / tau)) := by
    trans ∑ _i : ι, ENNReal.ofReal (c * Real.exp (-b / tau))
    · apply Finset.sum_congr rfl
      intro i _
      rw [hbudget i]
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmain := anyInvalid_measure_le_min_one_sum μ Vil Vih Vol Voh hVol
    hVilVih hVoh resolutionTime budget idealVoltage noise observedVoltage expectedBit hmodel
    hmeas c tau hc htau (fun i => by rw [hbudget i]; exact hb) htail
  rwa [hsum] at hmain

/-! ## E. Validation cases -/

/-- With no observations, there is no invalid observation: the union
over an empty index type is empty. -/
lemma measure_biUnion_invalidEvent_eq_zero_of_isEmpty {Ω : Type*}
    [MeasurableSpace Ω] {ι : Type*} [IsEmpty ι] (μ : Measure Ω)
    (Vil Vih : ℝ) (observedVoltage : ι → Ω → ℝ) :
    μ (⋃ i : ι, invalidEvent Vil Vih observedVoltage i) = 0 := by
  rw [Set.iUnion_of_empty, measure_empty]

/-- A voltage strictly between the thresholds is invalid: the concrete
mid-band voltage `3 / 2` for thresholds `1` and `2`. -/
lemma invalidObservation_one_two_three_halves :
    invalidObservation 1 2 (3 / 2) :=
  (observe_eq_none_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩

end PhyslibExt.Electronics.SynchronizerObservationBudget
