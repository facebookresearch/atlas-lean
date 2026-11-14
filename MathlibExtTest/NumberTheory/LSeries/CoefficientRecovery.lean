/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.CoefficientRecovery
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Tests for coefficient recovery by vertical mean values
-/

open Complex Filter Topology LSeries

@[expose] public section

/-- For `ζ` (`a = 1`), the mean value at the integer `y = 3` recovers `a 3 = 1`. -/
example : Tendsto (fun T : ℝ => (1 / (2 * T)) * ∫ t in -T..T,
      LSeries 1 ((2 : ℝ) + (t : ℂ) * I) * ((3 : ℝ) : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * I))
    atTop (𝓝 1) := by
  have h : abscissaOfAbsConv 1 < ((2 : ℝ) : EReal) := by
    rw [abscissaOfAbsConv_one]; exact_mod_cast (by norm_num : (1 : ℝ) < 2)
  have := tendsto_mean_vertical_mul_cpow 1 h (y := 3) (by norm_num)
  rwa [ite_eq_left ⟨3, by norm_num, by norm_num⟩] at this

/-- At a non-integer `y = 5/2` the mean value tends to `0`. -/
example : Tendsto (fun T : ℝ => (1 / (2 * T)) * ∫ t in -T..T,
      LSeries 1 ((2 : ℝ) + (t : ℂ) * I) * ((5 / 2 : ℝ) : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * I))
    atTop (𝓝 0) := by
  have h : abscissaOfAbsConv 1 < ((2 : ℝ) : EReal) := by
    rw [abscissaOfAbsConv_one]; exact_mod_cast (by norm_num : (1 : ℝ) < 2)
  have := tendsto_mean_vertical_mul_cpow 1 h (y := 5 / 2) (by norm_num)
  rwa [ite_eq_right] at this
  rintro ⟨n, -, hn⟩
  have h1 : (n : ℝ) * 2 = 5 := by rw [hn]; norm_num
  have h2 : n * 2 = 5 := by exact_mod_cast h1
  omega
