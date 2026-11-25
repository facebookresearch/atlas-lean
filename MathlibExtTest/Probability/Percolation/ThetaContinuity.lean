/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Percolation.ThetaContinuity

open MathlibExt.Probability.Percolation.ThetaContinuityWanted
open StatMech.Percolation
open scoped NNReal

-- In dimension zero, the critical point is the upper endpoint of the parameter interval.
example : ContinuousWithinAt (thetaOnUnit 0) {p | 1 ≤ p.1} ⟨1, le_rfl⟩ := by
  have hempty : percolationEvent 0 = ∅ := by
    ext ω
    simp only [mem_percolationEvent, Set.mem_empty_iff_false, iff_false, Set.not_infinite]
    exact Set.toFinite _
  have hpc : pc 0 = 1 :=
    le_antisymm pc_le_one (le_csSup subcriticalSet_bddAbove ⟨le_rfl, by simp [theta, hempty]⟩)
  have hpoint : (⟨pc 0, pc_le_one⟩ : {p : ℝ≥0 // p ≤ 1}) = ⟨1, le_rfl⟩ :=
    Subtype.ext hpc
  have h := theta_continuousWithinAt_pc (d := 0)
  rw [hpoint] at h
  simpa only [hpc] using h
