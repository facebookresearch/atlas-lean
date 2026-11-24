/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Optimization.BarzilaiBorwein
import Mathlib.Analysis.InnerProductSpace.PiL2

open MathlibExt.Analysis.Optimization.BarzilaiBorwein

-- On the one-dimensional quadratic `x²` (Hessian `2`), `y = 2 s` and both steps equal `1/2`,
-- the exact Newton step.
example : bbStep (1 : ℝ) 2 = 1 / 2 := by norm_num [bbStep]
example : bbStep₂ (1 : ℝ) 2 = 1 / 2 := by norm_num [bbStep₂]

-- With `s = (1, 0)` and `y = (1, 1)` the two steps differ: `bbStep₂ = 1/2 < 1 = bbStep`.
example : bbStep₂ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1, 1] ≤
    bbStep (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1, 1] :=
  bbStep₂_le_bbStep (by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two])

-- The Rayleigh bounds with `A = 3 I`: `α = 1/3`.
example (s : ℝ) (hs : s ≠ 0) :
    1 / 3 ≤ bbStep s ((3 : ℝ) • ContinuousLinearMap.id ℝ ℝ s) ∧
      bbStep s ((3 : ℝ) • ContinuousLinearMap.id ℝ ℝ s) ≤ 1 / 3 :=
  bbStep_mem_Icc (A := (3 : ℝ) • ContinuousLinearMap.id ℝ ℝ) (m := 3) (L := 3) (by norm_num)
    (fun v => le_of_eq (by simp; ring)) (fun v => le_of_eq (by simp; ring)) hs
