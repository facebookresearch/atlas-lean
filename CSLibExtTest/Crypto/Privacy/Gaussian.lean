/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Crypto.Privacy.Gaussian

open Cslib.Crypto.Privacy MeasureTheory ProbabilityTheory

namespace CSLibExtTest.Crypto.Privacy.Gaussian

private lemma calibration : 2 * Real.log ((5 / 4) / (1 / 2)) < (2 : ℝ) ^ 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (5 / 4) / (1 / 2) by norm_num)
  linarith

-- The scalar identity query attains sensitivity one for inputs at distance one.
example : DifferentiallyPrivate (fun x y : ℝ ↦ |x - y| ≤ 1)
    (fun x ↦ Measure.pi fun _ : Fin 1 ↦ gaussianReal x 16) (1 / 2) (ENNReal.ofReal (1 / 2)) := by
  have h := gaussianMechanism_differentiallyPrivate (ε := 1 / 2) (δ := 1 / 2) (c := 2)
    (f := fun x (_ : Fin 1) ↦ x) (Adj := fun x y : ℝ ↦ |x - y| ≤ 1)
    (Δ₂ := 1) (σ := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    calibration (by norm_num) (by intro x y h; simpa using h)
  convert h using 1
  norm_num

-- With zero sensitivity, the mechanism may release a deterministic vector.
example (m : Fin 2 → ℝ) : DifferentiallyPrivate (fun _ _ : Bool ↦ True)
    (fun _ ↦ Measure.pi fun i ↦ Measure.dirac (m i)) (1 / 2) (ENNReal.ofReal (1 / 2)) := by
  simpa using gaussianMechanism_differentiallyPrivate (ε := 1 / 2) (δ := 1 / 2) (c := 2)
    (f := fun _ : Bool ↦ m) (Adj := fun _ _ ↦ True) (Δ₂ := 0) (σ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    calibration (by norm_num) (by simp)

end CSLibExtTest.Crypto.Privacy.Gaussian
