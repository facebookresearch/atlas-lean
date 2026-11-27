/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.RademacherRiskBound

/-!
# Tests for the Rademacher risk bound

A two-observation sample checks the order of labels and predictions in the cost vectors.
For a singleton class the complexity penalty vanishes in the probability bound.
-/

namespace Cslib.MachineLearning.Rademacher

open MeasureTheory

example : costVectors (fun y a : ℝ => y - a) {fun x : ℝ => 2 * x}
    (![(1, 5), (3, 7)] : Fin 2 → ℝ × ℝ) = {![3, 1]} := by
  rw [costVectors, Set.image_singleton]
  congr 1
  funext i
  fin_cases i <;> norm_num

example {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (f : X → A) (L : Y → A → ℝ)
    (hL : ∀ y a, 0 ≤ L y a) (h1 : ∀ y a, L y a ≤ 1)
    (hm : Measurable fun z : X × Y => L z.2 (f z.1))
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - ENNReal.ofReal δ ≤ (Measure.pi fun _ : Fin n => P)
      {S | ∫ z, L z.2 (f z.1) ∂P ≤ (n : ℝ)⁻¹ * ∑ i, L (S i).2 (f (S i).1) +
        Real.sqrt (8 * Real.log (2 / δ) / n)} := by
  have h := risk_le_empirical_add_rademacher P L L hL h1 (fun _ _ => le_rfl)
    {f} (Set.finite_singleton f) (by simpa using hm) (by simpa using hm) hn hδ0 hδ1
  simpa [costVectors, rademacherComplexity_singleton] using h

end Cslib.MachineLearning.Rademacher
