/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Topology.MetricSpace.StdSimplex

-- The metric instance is inferred from an external module.
noncomputable example (n : ℕ) : MetricSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  inferInstance

-- Distance to a fixed simplex point is continuous in the canonical topology.
noncomputable example (n : ℕ) (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Continuous fun y => dist y x := by
  fun_prop

-- The simp lemma rewrites simplex distance to the Pi-space distance of weights.
noncomputable example (n : ℕ) (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist x y = dist (x.weights : Fin (n + 1) → ℝ) (y.weights : Fin (n + 1) → ℝ) := by
  simp
