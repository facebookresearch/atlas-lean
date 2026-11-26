/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.HippocratesLunes
import Mathlib.Tactic.NormNum

open MeasureTheory
namespace MathlibExt.Geometry.HippocratesLunesWanted.Geometry.HippocratesLunes

-- The outermost points of the two semicircular arcs belong to their respective lunes.
example : ((2, -2) : Plane) ∈ horizontalLune 4 2 ∧ ((-1, 1) : Plane) ∈ verticalLune 4 2 := by
  norm_num [horizontalLune, verticalLune, hypotenuseSemidisk, closedHalfDisk,
    euclideanDistSq, midpoint, det2, vec, A, B, C]

-- A point in the common circular segment is removed from the horizontal lune.
example : ((2, -1 / 2) : Plane) ∈ closedHalfDisk A (B 4) (· ≤ 0) ∧
    ((2, -1 / 2) : Plane) ∉ horizontalLune 4 2 := by
  norm_num [horizontalLune, hypotenuseSemidisk, closedHalfDisk,
    euclideanDistSq, midpoint, det2, vec, A, B, C]

-- The common endpoint lies in the triangle and is excluded from both closed-disk differences.
example : A ∈ rightTriangle 4 2 ∧ A ∉ horizontalLune 4 2 ∧ A ∉ verticalLune 4 2 := by
  refine ⟨subset_convexHull ℝ _ (Set.mem_insert _ _), ?_⟩
  norm_num [horizontalLune, verticalLune, hypotenuseSemidisk, closedHalfDisk,
    euclideanDistSq, midpoint, det2, vec, A, B, C]

example : volume (horizontalLune 4 2) + volume (verticalLune 4 2) = volume (rightTriangle 4 2) :=
  hippocrates_lunes (a := 4) (b := 2) (ha := by norm_num) (hb := by norm_num)

end MathlibExt.Geometry.HippocratesLunesWanted.Geometry.HippocratesLunes
