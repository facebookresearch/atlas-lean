/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import MathlibExt.Geometry.PlaneUnitDistanceSevenColor

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private noncomputable def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

private lemma dist_point_sq (x y x' y' : ℝ) :
    dist (point x y) (point x' y') ^ 2 = (x - x') ^ 2 + (y - y') ^ 2 := by
  simp [point, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

-- The circumcenter of an elementary triangle is equally close to all three sites.
example : dist (point (2 / 5) (2 / 15 * Real.sqrt 3)) (point 0 0) ^ 2 = 16 / 75 ∧
    dist (point (2 / 5) (2 / 15 * Real.sqrt 3)) (point (4 / 5) 0) ^ 2 = 16 / 75 ∧
    dist (point (2 / 5) (2 / 15 * Real.sqrt 3)) (point (2 / 5) (2 / 5 * Real.sqrt 3)) ^ 2 =
      16 / 75 ∧ (16 / 75 : ℝ) < (1 / 2) ^ 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  simp only [dist_point_sq]
  refine ⟨?_, ?_, ?_, by norm_num⟩ <;> nlinarith only [hs]

-- The offset (1, 2) has the same residue as the origin, but its site is over two units away.
example : ((1 + 3 * 2 : ℤ) % 7 = 0) ∧
    dist (point (8 / 5) (4 / 5 * Real.sqrt 3)) (point 0 0) ^ 2 = 112 / 25 ∧
    (2 : ℝ) < dist (point (8 / 5) (4 / 5 * Real.sqrt 3)) (point 0 0) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hd : dist (point (8 / 5) (4 / 5 * Real.sqrt 3)) (point 0 0) ^ 2 = 112 / 25 := by
    rw [dist_point_sq]
    nlinarith only [hs]
  refine ⟨by decide, hd, ?_⟩
  by_contra! h
  nlinarith only [hd, pow_le_pow_left₀ dist_nonneg h 2]

-- This horizontal unit edge starts at the three-way tie above.
example : ∃ c : Plane → Fin 7,
    c (point (2 / 5) (2 / 15 * Real.sqrt 3)) ≠ c (point (7 / 5) (2 / 15 * Real.sqrt 3)) := by
  obtain ⟨c, hc⟩ := EuclideanGeometry.exists_seven_coloring
  refine ⟨c, hc _ _ ?_⟩
  have hd : dist (point (2 / 5) (2 / 15 * Real.sqrt 3))
      (point (7 / 5) (2 / 15 * Real.sqrt 3)) ^ 2 = 1 := by rw [dist_point_sq]; norm_num
  nlinarith only [hd, dist_nonneg (x := point (2 / 5) (2 / 15 * Real.sqrt 3))
    (y := point (7 / 5) (2 / 15 * Real.sqrt 3))]
