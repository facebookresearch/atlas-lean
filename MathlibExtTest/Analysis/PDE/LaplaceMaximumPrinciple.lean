/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for the weak maximum principle for the Laplacian

* `Δ ‖x‖² = 4` on `ℝ²`.
* At the maximum `0` of `-‖x‖²` on `ℝ³` the Laplacian is nonpositive.
* The non-constant subharmonic function `‖x‖²` on the unit ball of `ℝ²` satisfies every
  hypothesis of the weak maximum principle, which then gives a boundary maximum.
-/

open InnerProductSpace Laplacian Set Metric
open MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

example (z : EuclideanSpace ℝ (Fin 2)) : Δ (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2) z = 4 := by
  rw [laplacian_norm_sq]
  simp
  norm_num

example : Δ (fun x : EuclideanSpace ℝ (Fin 3) => -‖x‖ ^ 2) 0 ≤ 0 := by
  refine laplacian_nonpos_of_isLocalMax (contDiff_norm_sq ℝ).neg.contDiffAt ?_
  exact Filter.Eventually.of_forall fun x => by simp

example : ∃ y ∈ frontier (ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
    IsMaxOn (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2)
      (closure (ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) y :=
  exists_mem_frontier_isMaxOn_of_laplacian_nonneg isOpen_ball isBounded_ball
    ⟨0, mem_ball_self one_pos⟩ (by fun_prop) (fun _ _ => (contDiff_norm_sq ℝ).contDiffAt)
    (fun z _ => by rw [laplacian_norm_sq]; positivity)
