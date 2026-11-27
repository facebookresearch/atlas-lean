/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.ADMMConvergence
import Mathlib.Tactic.Linarith

open Filter WantedExt.Analysis.Convex.ADMMConvergenceWanted

-- Minimize x subject to x = 0, with an arbitrary second block in the kernel of B.
-- Starting from y₀ = 0 gives x₁ = -1 and y₁ = -1, followed by xₖ = 0.
example (z : ℕ → ℝ) (initial : ℝ) :
    let x : ℕ → ℝ := fun k => if k = 0 then initial else if k = 1 then -1 else 0
    Tendsto x atTop (nhds 0) ∧ Tendsto (fun k => x k + 0) atTop (nhds 0) := by
  intro x
  let y (k : ℕ) : ℝ := if k = 0 then 0 else -1
  have h := admm_residual_and_objective_convergence (convexOn_id convex_univ)
    (convexOn_const (0 : ℝ) convex_univ) (ContinuousLinearMap.id ℝ ℝ) (0 : ℝ →L[ℝ] ℝ)
    0 (ρ := 1) one_pos (xs := 0) (zs := 0) (ys := -1) (x := x) (z := z) (y := y)
    (by simp) (by
      intro k v
      cases k <;> simp [x, y, Real.norm_eq_abs, sq_abs] <;>
        nlinarith [sq_nonneg (v + 1), sq_nonneg v])
    (by simp) (by
      intro k
      cases k <;> simp [x, y])
  simpa using h
