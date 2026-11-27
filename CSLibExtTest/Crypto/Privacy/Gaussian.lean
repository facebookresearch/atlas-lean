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

-- The calibration tail estimate at the parameters of the first example: noise scale `σ = 4` and
-- sensitivity `1` give the standardized shift `r = 1 / 4 = ε / c`, so the standard normal mass
-- above the threshold `ε / r - r / 2 = 15 / 8` is at most `δ = 1 / 2`.
example : gaussianReal 0 1 (Set.Ioi (15 / 8 : ℝ)) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  have h := gaussian_calibration_tail_le (ε := 1 / 2) (δ := 1 / 2) (c := 2) (r := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) calibration (by norm_num)
    (by norm_num)
  rwa [show ((1 / 2 : ℝ) / (1 / 4) - (1 / 4) / 2) = 15 / 8 by norm_num] at h

-- The calibration tail estimate with `c - ε / (2 * c) ≥ 0`: `ε = r = 1 / 2`, `c = 1` and
-- `δ = 99 / 100` give the threshold `3 / 4`.
example : gaussianReal 0 1 (Set.Ioi (3 / 4 : ℝ)) ≤ ENNReal.ofReal (99 / 100 : ℝ) := by
  have hlog : Real.log ((5 / 4 : ℝ) / (99 / 100)) ≤ 26 / 99 := by
    have h :=
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < (5 / 4) / (99 / 100) by norm_num)
    have hfrac : ((5 / 4 : ℝ) / (99 / 100)) - 1 = 26 / 99 := by norm_num
    linarith
  have hc : 2 * Real.log ((5 / 4 : ℝ) / (99 / 100)) < (1 : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h1]
    linarith
  have h :=
    gaussian_calibration_tail_le (ε := (1 / 2 : ℝ)) (δ := (99 / 100 : ℝ))
      (c := (1 : ℝ)) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hc (by norm_num) (by norm_num)
  have hth : ((1 / 2 : ℝ) / (1 / 2) - (1 / 2) / 2) = 3 / 4 := by norm_num
  rwa [hth] at h

-- The calibration tail estimate with `c - ε / (2 * c) < 0`: `ε = δ = 99 / 100`, `c = 7 / 10` and
-- `r = 99 / 70` give the negative threshold `-1 / 140`.
example : gaussianReal 0 1 (Set.Ioi (-1 / 140 : ℝ)) ≤ ENNReal.ofReal (99 / 100 : ℝ) := by
  have hexp : (125 / 99 : ℝ) < Real.exp (49 / 200) := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 49 / 200 by norm_num)
    have hnum : (125 / 99 : ℝ) < 1 + 49 / 200 + (49 / 200) ^ 2 / 2 := by norm_num
    linarith
  have hlog : Real.log (125 / 99 : ℝ) < 49 / 200 := by
    have h := Real.log_lt_log (show (0 : ℝ) < 125 / 99 by norm_num) hexp
    rwa [Real.log_exp] at h
  have hfrac : ((5 / 4 : ℝ) / (99 / 100)) = 125 / 99 := by norm_num
  have hc : 2 * Real.log ((5 / 4 : ℝ) / (99 / 100)) < (7 / 10 : ℝ) ^ 2 := by
    rw [hfrac]
    have hsq : (7 / 10 : ℝ) ^ 2 = 49 / 100 := by norm_num
    rw [hsq]
    linarith
  have h :=
    gaussian_calibration_tail_le (ε := (99 / 100 : ℝ)) (δ := (99 / 100 : ℝ))
      (c := (7 / 10 : ℝ)) (r := (99 / 70 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hc (by norm_num) (by norm_num)
  have hth : ((99 / 100 : ℝ) / (99 / 70) - (99 / 70) / 2) = -1 / 140 := by norm_num
  rwa [hth] at h

-- The calibration tail estimate when `δ ≥ 1`.
example : gaussianReal 0 1 (Set.Ioi (3 / 4 : ℝ)) ≤ ENNReal.ofReal (2 : ℝ) := by
  have hlog : Real.log ((5 / 4 : ℝ) / 2) ≤ 0 :=
    Real.log_nonpos (by norm_num) (by norm_num)
  have hc : 2 * Real.log ((5 / 4 : ℝ) / 2) < (1 : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h1]
    linarith
  have h :=
    gaussian_calibration_tail_le (ε := (1 / 2 : ℝ)) (δ := (2 : ℝ)) (c := (1 : ℝ))
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hc (by norm_num) (by norm_num)
  have hth : ((1 / 2 : ℝ) / (1 / 2) - (1 / 2) / 2) = 3 / 4 := by norm_num
  rwa [hth] at h

end CSLibExtTest.Crypto.Privacy.Gaussian
