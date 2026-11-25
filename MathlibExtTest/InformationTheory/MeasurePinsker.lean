/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MeasurePinsker
public import MathlibExt.InformationTheory.Pinsker

@[expose] public section

/-!
# Tests for total variation, optimal tests and Pinsker's inequality

* `binary_pinsker_of_mem_Icc` at the endpoint `u = 0`, which the strictly positive
  `csiszar_kullback_pinsker` cannot reach: `1/2 ≤ log 2`.
* `tvDist_eq_two_mul_totalVariationDist` on two distinct point masses: `tvDist = 2`.
* The optimal-test identity and Pinsker on point masses, where `D = ∞` while `TV = 1`.
* Pinsker gives `TV ≤ √(D / 2)` for any pair with finite divergence.
-/

open MeasureTheory Real
open MathlibExt.Probability.TotalVariationDistance MathlibExt.InformationTheory.MeasurePinsker

namespace MathlibExtTest.InformationTheory.MeasurePinsker

/-- Binary Pinsker at `u = 0`, `v = 1/2`: `2 (1/2)² ≤ log 2`. -/
example : 2 * ((0 : ℝ) - 1 / 2) ^ 2 ≤
    0 * Real.log (0 / (1 / 2)) + (1 - 0) * Real.log ((1 - 0) / (1 - 1 / 2)) :=
  MathlibExt.InformationTheory.Pinsker.binary_pinsker_of_mem_Icc le_rfl zero_le_one
    (by norm_num) (by norm_num)

/-- Two distinct point masses are at Mathlib total variation distance `2`. -/
example : tvDist (Measure.dirac true) (Measure.dirac false) = 2 := by
  classical
  rw [tvDist_eq_two_mul_totalVariationDist, totalVariationDist_dirac]
  simp

/-- The optimal test between distinct point masses has total error `1 - TV = 0`. -/
example : ∃ A : Set Bool, MeasurableSet A ∧
    (Measure.dirac true).real A + (Measure.dirac false).real Aᶜ = 0 := by
  classical
  obtain ⟨A, hA, h⟩ :=
    exists_add_compl_eq_one_sub_totalVariationDist (μ := Measure.dirac true)
      (ν := Measure.dirac false)
  refine ⟨A, hA, ?_⟩
  rw [h, totalVariationDist_dirac]
  simp

/-- Pinsker between distinct point masses: `2 ≤ D(δ_true ‖ δ_false)`. -/
example : ENNReal.ofReal 2 ≤
    InformationTheory.klDiv (Measure.dirac true) (Measure.dirac false) := by
  classical
  have h := ofReal_two_mul_totalVariationDist_sq_le_klDiv (Measure.dirac true)
    (Measure.dirac false)
  rw [totalVariationDist_dirac] at h
  simpa using h

/-- The square-root form, for an arbitrary pair with finite divergence. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : InformationTheory.klDiv μ ν ≠ ⊤) :
    totalVariationDist μ ν ≤ √((InformationTheory.klDiv μ ν).toReal / 2) :=
  totalVariationDist_le_sqrt_klDiv h

end MathlibExtTest.InformationTheory.MeasurePinsker
