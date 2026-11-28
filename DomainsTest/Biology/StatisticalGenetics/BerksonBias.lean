/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.BerksonBias
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.NormNum

open Filter Topology

open WantedExt.Biology.StatisticalGenetics.BerksonBiasWanted

-- With all five parameters equal to 1/2, the admitted odds ratio is 7/9.
example :
    ((1 / 2 : ℝ) * (1 / 2) * (1 - (1 / 2) * (1 / 2) * (1 / 2))) *
        ((1 - 1 / 2) * (1 - 1 / 2) * (1 - 1 / 2)) /
          (((1 / 2) * (1 - 1 / 2) * (1 - (1 / 2) * (1 / 2))) *
            ((1 - 1 / 2) * (1 / 2) * (1 - (1 / 2) * (1 / 2)))) = 7 / 9 := by
  rw [(hospitalOddsRatio (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1]
  norm_num

-- At t₀ = 1, people with neither disease are never admitted, so the ratio is zero.
example :
    ((1 / 2 : ℝ) * (1 / 2) * (1 - 1 * (1 / 2) * (1 / 2))) *
        ((1 - 1 / 2) * (1 - 1 / 2) * (1 - 1)) /
          (((1 / 2) * (1 - 1 / 2) * (1 - 1 * (1 / 2))) *
            ((1 - 1 / 2) * (1 / 2) * (1 - 1 * (1 / 2)))) = 0 := by
  rw [(hospitalOddsRatio (1 / 2) (1 / 2) (1 / 2) (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1]
  norm_num

-- Compute both ratios at the lower endpoint and at an interior point.
example : (1 - (0 : ℝ) ^ 2) / (1 - 0) = 1 ∧ (1 - (0 : ℝ) ^ 3) / (1 - 0) = 1 := by
  norm_num

example : (1 - (1 / 2 : ℝ) ^ 2) / (1 - 1 / 2) = 3 / 2 ∧
    (1 - (1 / 2 : ℝ) ^ 3) / (1 - 1 / 2) = 7 / 4 := by
  norm_num

-- Independently compute both left limits as derivatives of powers at 1.
example :
    Tendsto (fun t : ℝ => (1 - t ^ 2) / (1 - t)) (𝓝[<] 1) (𝓝 2) ∧
    Tendsto (fun t : ℝ => (1 - t ^ 3) / (1 - t)) (𝓝[<] 1) (𝓝 3) := by
  have limitFromDerivative (n : ℕ) :
      Tendsto (fun t : ℝ => (1 - t ^ n) / (1 - t)) (𝓝[<] 1) (𝓝 (n : ℝ)) := by
    have h := (hasDerivAt_pow n (1 : ℝ)).tendsto_slope.mono_left (nhdsLT_le_nhdsNE 1)
    simp only [slope_fun_def_field, one_pow, mul_one] at h
    refine h.congr fun t => ?_
    simpa only [neg_sub] using (neg_div_neg_eq (t ^ n - 1) (t - 1)).symm
  exact ⟨limitFromDerivative 2, limitFromDerivative 3⟩

-- A client can apply both closed forms at a common non-selection probability of 9/10.
example : (1 - (9 / 10 : ℝ) ^ 2) / (1 - 9 / 10) = 19 / 10 ∧
    (1 - (9 / 10 : ℝ) ^ 3) / (1 - 9 / 10) = 271 / 100 := by
  obtain ⟨h₂, h₃⟩ := admission_ratios.1 (9 / 10) (by norm_num) (by norm_num)
  rw [h₂, h₃]
  norm_num
