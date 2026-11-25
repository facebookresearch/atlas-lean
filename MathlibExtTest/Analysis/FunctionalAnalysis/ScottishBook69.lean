/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69Wanted

-- Coincident endpoints give a singleton at every stage, including the initial metric segment.
example {E : Type*} [MetricSpace E] (p : E) : IsMetricCenter E p p p := by
  have hs (n : ℕ) : metricCenterSets E p p n = {p} := by
    induction n with
    | zero =>
      ext x
      change (dist p x + dist x p = dist p p) ↔ x = p
      rw [dist_comm p x, dist_self, ← two_mul, mul_eq_zero]
      simp
    | succ n ih => rw [metricCenterSets, ih]; simp
  exact ⟨fun n => by simp [hs], fun y hy => by simpa [hs] using hy 0⟩

-- The universal assertion entails a contradiction even with the nonemptiness hypothesis.
example (h : ScottishBookProblem69Claim) : False := mazurUlam69_refuted h
