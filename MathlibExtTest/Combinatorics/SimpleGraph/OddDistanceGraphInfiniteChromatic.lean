/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.OddDistanceGraphInfiniteChromatic
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.OddDistanceGraphInfiniteChromatic

open MathlibExt.GraphTheory.OddDistanceGraphInfiniteChromaticWanted
open ODGIC

private noncomputable def axisPoint (x : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[x, 0]

private lemma dist_axisPoint (x y : ℝ) : dist (axisPoint x) (axisPoint y) = |x - y| := by
  rw [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, axisPoint, sq_abs]

example : OddDistanceGraph.Adj (axisPoint 0) (axisPoint 1) := by
  refine ⟨1, odd_one, ?_⟩
  norm_num [dist_axisPoint]

example : OddDistanceGraph.Adj (axisPoint 3) (axisPoint 0) := by
  refine ⟨3, ⟨1, by decide⟩, ?_⟩
  norm_num [dist_axisPoint]

example : ¬OddDistanceGraph.Adj (axisPoint 0) (axisPoint 2) := by
  rintro ⟨k, hk, hdist⟩
  have h : (k : ℝ) = 2 := by norm_num [dist_axisPoint] at hdist; exact hdist.symm
  have hk₂ : k = 2 := by exact_mod_cast h
  exact (by decide : ¬Odd (2 : ℕ)) (hk₂ ▸ hk)

example : ¬OddDistanceGraph.Adj (axisPoint 0) (axisPoint 0) := by simp

example (k : ℕ) : ¬OddDistanceGraph.Colorable k := by
  intro h
  exact (SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨k, h⟩)
    OddDistanceChromaticInfinite_holds

end MathlibExtTest.OddDistanceGraphInfiniteChromatic
