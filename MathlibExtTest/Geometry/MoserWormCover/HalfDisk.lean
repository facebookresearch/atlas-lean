/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.MoserWormCover.HalfDisk

/-! # Tests for the disk of diameter one covering every unit arc -/

open MoserConvexWormCoverConstant

-- The claim unfolds to the covering property of `halfDisk`.
example : CoversEveryUnitArc halfDisk := halfDiskCovers_holds

-- A closed disk about `0` covers every unit arc exactly when its radius is at least `1/2`: larger
-- disks contain `halfDisk`, and a smaller disk cannot hold the two endpoints of the straight unit
-- arc, which are at distance `1`.
example (r : ℝ) : CoversEveryUnitArc (Metric.closedBall (0 : ℂ) r) ↔ 1 / 2 ≤ r := by
  constructor
  · intro h
    obtain ⟨angle, translation, hm⟩ := h straightUnitArc
    have h0 := Metric.mem_closedBall.1 (hm 0)
    have h1 := Metric.mem_closedBall.1 (hm 1)
    have hd : dist (move angle translation (straightUnitArc.path 0))
        (move angle translation (straightUnitArc.path 1)) = 1 := by
      rw [(move_isometry angle translation).dist_eq]
      simp [straightUnitArc, straightPath, Complex.dist_eq]
    linarith [dist_triangle_right (move angle translation (straightUnitArc.path 0))
      (move angle translation (straightUnitArc.path 1)) 0]
  · intro hr arc
    obtain ⟨angle, translation, hm⟩ := halfDiskCovers_holds arc
    refine ⟨angle, translation, fun t => mem_closedBall_zero_iff.2 ?_⟩
    have ht : ‖move angle translation (arc.path t)‖ ≤ (1 : ℝ) / 2 := hm t
    linarith
