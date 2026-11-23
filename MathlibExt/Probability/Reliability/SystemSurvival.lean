/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Series and parallel system survival

## i. Overview

For component lifetimes `T i` on a common probability space, the
parallel system survives load level `x` when at least one component
does. Under mutual independence (`iIndepFun`) of measurable
lifetimes, the parallel survival is one minus the product of
component failure probabilities. Without independence, the
parallel survival is still bounded by the sum of component
survivals (union bound); no independence is inferred from
component labels. Series survival under independence is the
existing `measureReal_forall_lt_eq_prod`.

## ii. Key results

- `Reliability.parallel_survival_eq`: parallel survival under
  mutual independence.
- `Reliability.parallel_survival_le_sum`: the union bound, with
  no independence hypothesis.

## iii. Table of contents

- A. Parallel survival and the union bound

## iv. References

- Standard system-reliability event algebra for series and
  parallel structures (independent component lifetimes).
-/

@[expose] public section

namespace Reliability

open MeasureTheory Set Filter Finset

/-! ## A. Parallel survival and the union bound -/

open MeasureTheory Set Filter Finset

/-- Parallel survival under mutual independence: one minus the
product of component failure probabilities. -/
theorem parallel_survival_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {T : ℕ → Ω → ℝ} (hT : ProbabilityTheory.iIndepFun T P)
    (hmeas : ∀ i, Measurable (T i)) (n : ℕ) (x : ℝ) :
    P.real {ω | ∃ i < n, x < T i ω}
      = 1 - ∏ i ∈ Finset.range n, (1 - P.real {ω | x < T i ω}) := by
  have hcompl : {ω | ∃ i < n, x < T i ω} = {ω | ∀ i < n, T i ω ≤ x}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_le, exists_prop]
  have hset : {ω | ∀ i < n, T i ω ≤ x}
      = ⋂ i ∈ Finset.range n, T i ⁻¹' Set.Iic x := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic,
      Finset.mem_range]
  have hmeas_fail : MeasurableSet {ω | ∀ i < n, T i ω ≤ x} := by
    rw [hset]
    exact Finset.measurableSet_biInter _ (fun i _ => (hmeas i) measurableSet_Iic)
  rw [hcompl, MeasureTheory.probReal_compl_eq_one_sub hmeas_fail]
  congr 1
  rw [hset, measureReal_def, hT.measure_inter_preimage_eq_mul (Finset.range n)
    (sets := fun _ => Set.Iic x) (fun _ _ => measurableSet_Iic), ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : T i ⁻¹' Set.Iic x = {ω | x < T i ω}ᶜ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  have hmeas_i : MeasurableSet {ω | x < T i ω} := (hmeas i) measurableSet_Ioi
  rw [hi, ← measureReal_def,
    MeasureTheory.probReal_compl_eq_one_sub hmeas_i]

/-- Union bound, with no independence hypothesis: parallel
survival is at most the sum of component survivals. -/
theorem parallel_survival_le_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {T : ℕ → Ω → ℝ} (n : ℕ) (x : ℝ) :
    P.real {ω | ∃ i < n, x < T i ω}
      ≤ ∑ i ∈ Finset.range n, P.real {ω | x < T i ω} := by
  have hset : {ω | ∃ i < n, x < T i ω}
      = ⋃ i ∈ Finset.range n, {ω | x < T i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
  rw [hset]
  exact MeasureTheory.measureReal_biUnion_finset_le _ _

/-- Parallel survival under mutual independence over a finite
component set: one minus the product of component failure
probabilities. This is the finite-set form of
`parallel_survival_eq`. -/
theorem parallel_survival_eq_finset {Ω ι : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {T : ι → Ω → ℝ} (hT : ProbabilityTheory.iIndepFun T P)
    (hmeas : ∀ i, Measurable (T i)) (s : Finset ι) (x : ℝ) :
    P.real {ω | ∃ i ∈ s, x < T i ω}
      = 1 - ∏ i ∈ s, (1 - P.real {ω | x < T i ω}) := by
  have hcompl : {ω | ∃ i ∈ s, x < T i ω} = {ω | ∀ i ∈ s, T i ω ≤ x}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_le,
      exists_prop]
  have hset : {ω | ∀ i ∈ s, T i ω ≤ x}
      = ⋂ i ∈ s, T i ⁻¹' Set.Iic x := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage,
      Set.mem_Iic]
  have hmeas_fail : MeasurableSet {ω | ∀ i ∈ s, T i ω ≤ x} := by
    rw [hset]
    exact Finset.measurableSet_biInter _ (fun i _ => (hmeas i) measurableSet_Iic)
  rw [hcompl, MeasureTheory.probReal_compl_eq_one_sub hmeas_fail]
  congr 1
  rw [hset, measureReal_def, hT.measure_inter_preimage_eq_mul s
    (sets := fun _ => Set.Iic x) (fun _ _ => measurableSet_Iic),
    ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : T i ⁻¹' Set.Iic x = {ω | x < T i ω}ᶜ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_compl_iff,
      Set.mem_ofPred_eq, not_lt]
  have hmeas_i : MeasurableSet {ω | x < T i ω} := (hmeas i) measurableSet_Ioi
  rw [hi, ← measureReal_def,
    MeasureTheory.probReal_compl_eq_one_sub hmeas_i]

/-- Union bound over a finite component set, with no independence
hypothesis. This is the finite-set form of
`parallel_survival_le_sum`. -/
theorem parallel_survival_le_sum_finset {Ω ι : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {T : ι → Ω → ℝ} (s : Finset ι)
    (x : ℝ) :
    P.real {ω | ∃ i ∈ s, x < T i ω}
      ≤ ∑ i ∈ s, P.real {ω | x < T i ω} := by
  have hset : {ω | ∃ i ∈ s, x < T i ω}
      = ⋃ i ∈ s, {ω | x < T i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [hset]
  exact MeasureTheory.measureReal_biUnion_finset_le _ _

end Reliability
