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
and the `p = 0` / `p = 1` and `n = 0` boundaries.

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

/-- `p = 0`: five certain no-exceedance events have probability `1`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (μ (⋂ _ : Fin 5, (Set.univ : Set Ω))).toReal = 1 := by
  have hIndep : iIndepSet (fun _ : Fin 5 => (Set.univ : Set Ω)) μ := by
    apply (iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.univ)).2
    intro s
    simp
  simpa only [sub_zero, one_pow] using
    (EarthScience.no_exceedance_prob (μ := μ) (p := 0)
      (F := fun _ : Fin 5 => (Set.univ : Set Ω))
      (by norm_num) (fun _ => MeasurableSet.univ) hIndep (by intro i; simp))

/-- `p = 1`: three impossible no-exceedance events have probability `0`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (μ (⋂ _ : Fin 3, (∅ : Set Ω))).toReal = 0 := by
  have hIndep : iIndepSet (fun _ : Fin 3 => (∅ : Set Ω)) μ := by
    apply (iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.empty)).2
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have hInter : (⋂ i ∈ s, (∅ : Set Ω)) = ∅ := by
        obtain ⟨i, hi⟩ := hs
        exact Set.eq_empty_of_subset_empty
          (Set.iInter_subset_of_subset i (Set.iInter_subset _ hi))
      simp [hInter, Finset.card_ne_zero.mpr hs]
  simpa only [sub_self, zero_pow (by decide : 3 ≠ 0)] using
    (EarthScience.no_exceedance_prob (μ := μ) (p := 1)
      (F := fun _ : Fin 3 => (∅ : Set Ω))
      (by norm_num) (fun _ => MeasurableSet.empty) hIndep (by intro i; simp))

/-- `n = 0`: an empty observation window has probability `1`, even at `p = 1`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) :
    (μ (⋂ _ : Fin 0, (∅ : Set Ω))).toReal = 1 := by
  have hIndep : iIndepSet (fun _ : Fin 0 => (∅ : Set Ω)) μ := by
    apply (iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.empty)).2
    intro s
    have hs : s = ∅ := Subsingleton.elim _ _
    simp [hs]
  simpa only [pow_zero] using
    (EarthScience.no_exceedance_prob (μ := μ) (p := p)
      (F := fun _ : Fin 0 => (∅ : Set Ω))
      hp (fun _ => MeasurableSet.empty) hIndep (fun i => Fin.elim0 i))
