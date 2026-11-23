/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ProductMoments
public import MathlibExt.Probability.FiniteProbability

/-!
# Product-law mass tests

Nonvacuity instances for the finite product law: rational two-item moments,
deterministic coordinates, and the empty index type.
-/

open MeasureTheory
open MathlibExt.Probability.Statistics.Measurement

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement

theorem fin2_hq0 : ∀ i : Fin 2, (0 : ℝ) ≤ (if i = 0 then (1 / 3 : ℝ) else (2 / 5 : ℝ)) := by
  intro i
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]
    norm_num

theorem fin2_hq1 : ∀ i : Fin 2, (if i = 0 then (1 / 3 : ℝ) else (2 / 5 : ℝ)) ≤ 1 := by
  intro i
  by_cases hi : i = 0 <;> simp [hi] <;> norm_num

/-- Two-item rational law: first moments `1/3`, `2/5`, pair moment `1/3*2/5`,
and total real mass `1`. -/
theorem localIndepPMF_fin2_moments : (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂(localIndepPMF (fun i : Fin 2 => if i = 0 then (1 / 3 : ℝ) else (2 / 5 : ℝ))
        (fin2_hq0) (fin2_hq1)).toMeasure = 1 / 3)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
      ∂(localIndepPMF (fun i : Fin 2 => if i = 0 then (1 / 3 : ℝ) else (2 / 5 : ℝ))
        (fin2_hq0) (fin2_hq1)).toMeasure = (1 / 3 : ℝ) * (2 / 5))
    ∧ (∑ x, (localIndepPMF (fun i : Fin 2 => if i = 0 then (1 / 3 : ℝ) else (2 / 5 : ℝ))
        (fin2_hq0) (fin2_hq1) x).toReal = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (localIndepPMF_coordinate_moments
      (fun i : Fin 2 => if i = 0 then (1 / 3 : ℝ) else (2 / 5 : ℝ)) fin2_hq0 fin2_hq1).1 0
    simpa using h
  · have h01 : (0 : Fin 2) ≠ 1 := by decide
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h := (localIndepPMF_coordinate_moments
      (fun i : Fin 2 => if i = 0 then (1 / 3 : ℝ) else (2 / 5 : ℝ)) fin2_hq0 fin2_hq1).2 0 1 h01
    simpa [h10] using h
  · exact MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one _

/-- Deterministic coordinates `q ≡ 1` and `q ≡ 0`: means `1` and `0`. -/
theorem localIndepPMF_deterministic_moments : (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂(localIndepPMF (fun _ : Fin 2 => (1 : ℝ)) (fun _ => zero_le_one) (fun _ => le_refl 1)).toMeasure = 1)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂(localIndepPMF (fun _ : Fin 2 => (0 : ℝ)) (fun _ => le_refl 0) (fun _ => zero_le_one)).toMeasure = 0) := by
  refine ⟨?_, ?_⟩
  · have h := (localIndepPMF_coordinate_moments (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => zero_le_one) (fun _ => le_refl 1)).1 0
    simpa using h
  · have h := (localIndepPMF_coordinate_moments (fun _ : Fin 2 => (0 : ℝ))
      (fun _ => le_refl 0) (fun _ => zero_le_one)).1 0
    simpa using h

/-- Empty index type: the unique outcome has real mass `1` (empty product). -/
theorem localIndepPMF_empty_mass (x : Fin 0 → Bool) :
    (localIndepPMF (fun _ : Fin 0 => (1 / 2 : ℝ)) (fun i => i.elim0) (fun i => i.elim0) x).toReal
      = 1 := by
  rw [localIndepPMF_toReal_apply]
  simp

end MathlibExtTest.Probability.Statistics.Measurement
