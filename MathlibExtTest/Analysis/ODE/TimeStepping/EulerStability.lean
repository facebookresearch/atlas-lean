/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.TimeStepping.EulerStability

open Filter Topology
open MathlibExt.Analysis.ODE.TimeStepping

-- Positive instance inside the threshold: `lam = -1`, `h = 1 / 2 < 2 / |-1|`.
-- The factor is `1 / 2`, and an importing client gets convergence for the
-- concrete initial value `x0 = 5` directly from the threshold theorem.
example : Tendsto (fun n : ℕ => (1 + (1 / 2 : ℝ) * (-1)) ^ n * (5 : ℝ)) atTop (𝓝 0) :=
  (scalarEuler_real_tendsto_zero_iff (lam := (-1 : ℝ)) (h := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)).mpr (by norm_num) 5

-- The roadmap's positive validation case `lam = -1`, `h = 1`: the factor is
-- `0`, so every initial value is sent to `0` after one step.
example : ∀ x0 : ℝ, Tendsto (fun n : ℕ => (1 + (1 : ℝ) * (-1)) ^ n * x0) atTop (𝓝 0) :=
  (scalarEuler_real_tendsto_zero_iff (lam := (-1 : ℝ)) (h := (1 : ℝ))
    (by norm_num) (by norm_num)).mpr (by norm_num)

-- Boundary `h = 2 / |lam|` is excluded: at `lam = -1`, `h = 2` the factor is
-- `-1`, so convergence for every initial value fails.
example : ¬ ∀ x0 : ℝ, Tendsto (fun n : ℕ => (1 + (2 : ℝ) * (-1)) ^ n * x0) atTop (𝓝 0) := by
  intro hall
  have hlt := (scalarEuler_real_tendsto_zero_iff (lam := (-1 : ℝ)) (h := (2 : ℝ))
    (by norm_num) (by norm_num)).mp hall
  norm_num at hlt

-- Above the threshold, `lam = -1`, `h = 3` (factor `-2`) also fails.
example : ¬ ∀ x0 : ℝ, Tendsto (fun n : ℕ => (1 + (3 : ℝ) * (-1)) ^ n * x0) atTop (𝓝 0) := by
  intro hall
  have hlt := (scalarEuler_real_tendsto_zero_iff (lam := (-1 : ℝ)) (h := (3 : ℝ))
    (by norm_num) (by norm_num)).mp hall
  norm_num at hlt

-- Complex instance: `lam = -1`, `h = 1` has amplification factor `0`.
example : ∀ x0 : ℂ, Tendsto (fun n : ℕ => (1 + ((1 : ℝ) : ℂ) * (-1)) ^ n * x0) atTop (𝓝 0) :=
  (scalarEuler_complex_tendsto_zero_iff (lam := (-1 : ℂ)) (h := (1 : ℝ))
    (by norm_num)).mpr (by norm_num)

#print axioms scalarEuler_complex_tendsto_zero_iff
#print axioms scalarEuler_real_tendsto_zero_iff
