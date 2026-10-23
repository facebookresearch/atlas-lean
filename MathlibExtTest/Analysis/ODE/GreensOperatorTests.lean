/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.GreensOperator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tests for the Green's operator on `[0, 1]`

* The Green's kernel is symmetric, nonnegative on `[0, 1]²`, vanishes
  when either argument is an endpoint, and is at most `1 / 4` on `[0, 1]²`.
* The first sine basis function takes the value `√2` at `x = 1 / 2` and
  vanishes at `x = 0`; the first eigenvalue is `1 / π²`.
* The kernel integral identity at `k = 1`, `x = 1 / 2` evaluates to
  `√2 / π²`, exercising `greens_kernel_integral_sine_eq` at a concrete point.
-/

namespace MathlibExtTest.Analysis.ODE.GreensOperatorTests

open MathlibExt.Analysis.ODE.GreensOperator

/-- The Green's kernel is symmetric. -/
example (x t : ℝ) : greensKernel x t = greensKernel t x := by
  simp only [greensKernel, min_comm x t, max_comm x t]

/-- The Green's kernel is nonnegative on `[0, 1]²`. -/
example {x t : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ greensKernel x t := by
  unfold greensKernel
  apply mul_nonneg (le_min hx.1 ht.1)
  exact sub_nonneg.mpr (max_le hx.2 ht.2)

/-- The Green's kernel vanishes when the first argument is `0`
and the second lies in `[0, 1]`. -/
example {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : greensKernel 0 t = 0 := by
  simp [greensKernel, min_eq_left ht.1]

/-- The Green's kernel vanishes when the second argument is `1`
and the first lies in `[0, 1]`. -/
example {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : greensKernel x 1 = 0 := by
  simp [greensKernel, max_eq_right hx.2]

/-- The Green's kernel is at most `1 / 4` on `[0, 1]²`. -/
example {x t : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    greensKernel x t ≤ 1 / 4 := by
  unfold greensKernel
  have hmin : min x t ≤ 1 := le_trans (min_le_left _ _) hx.2
  have hmax : min x t ≤ max x t := min_le_max
  have h1 : min x t * (1 - max x t) ≤ min x t * (1 - min x t) := by
    apply mul_le_mul_of_nonneg_left _ (le_min hx.1 ht.1)
    linarith
  have h2 : min x t * (1 - min x t) ≤ 1 / 4 := by
    have h : (min x t - 1 / 2) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  exact h1.trans h2

/-- The first sine basis function vanishes at `0`. -/
example : sineBasisFun 1 0 = 0 := by
  simp [sineBasisFun]

/-- The first sine basis function takes the value `√2` at `1 / 2`. -/
example : sineBasisFun 1 (1 / 2) = Real.sqrt 2 := by
  have h : (↑(1 : ℕ+) : ℝ) * Real.pi * (1 / 2) = Real.pi / 2 := by norm_num; ring
  simp only [sineBasisFun, h, Real.sin_pi_div_two, mul_one]

/-- The first Green's eigenvalue is `1 / π²`. -/
example : greensEigenvalue 1 = 1 / Real.pi ^ 2 := by
  simp [greensEigenvalue]

/-- The second Green's eigenvalue is `1 / (4π²)`. -/
example : greensEigenvalue 2 = 1 / (4 * Real.pi ^ 2) := by
  simp [greensEigenvalue]
  ring

/-- Every Green's eigenvalue is positive. -/
example (k : ℕ+) : 0 < greensEigenvalue k := by
  unfold greensEigenvalue
  positivity

/-- The kernel integral at `k = 1`, `x = 1 / 2` evaluates to `√2 / π²`. -/
example :
    ∫ t in (0 : ℝ)..1, greensKernel (1 / 2) t * sineBasisFun 1 t =
      Real.sqrt 2 / Real.pi ^ 2 := by
  rw [greens_kernel_integral_sine_eq 1 (1 / 2) (by norm_num) (by norm_num)]
  have h : (↑(1 : ℕ+) : ℝ) * Real.pi * (1 / 2) = Real.pi / 2 := by norm_num; ring
  have hs : sineBasisFun 1 (1 / 2) = Real.sqrt 2 := by
    simp only [sineBasisFun, h, Real.sin_pi_div_two, mul_one]
  have he : greensEigenvalue 1 = 1 / Real.pi ^ 2 := by simp [greensEigenvalue]
  rw [hs, he]
  ring

end MathlibExtTest.Analysis.ODE.GreensOperatorTests
