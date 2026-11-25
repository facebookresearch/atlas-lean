/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.Basis.Fin
import MathlibExt.Combinatorics.CleanLatticeParallelogram.Reflection

/-! # Point reflection on the shared antidiagonal of the unit square -/

open MetaMathlibExt

-- The shared edge belongs to both closed triangles away from the square's boundary.
example :
    ((3 / 4, 1 / 4) : ℝ × ℝ) ∈ convexHull ℝ {(1, 0), (0, 1), (1, 1)} ∩
      interior (latticeParallelogram (1, 0) (0, 1)) := by
  let u : ℝ × ℝ := (1, 0)
  let v : ℝ × ℝ := (0, 1)
  have huv : LinearIndependent ℝ ![u, v] := by
    convert (Module.Basis.finTwoProd ℝ).linearIndependent using 1
    ext i : 1
    fin_cases i <;> simp [u, v]
  have htriangle : ((1 / 4, 3 / 4) : ℝ × ℝ) ∈ convexHull ℝ {0, u, v} := by
    have hu := subset_convexHull ℝ {0, u, v} (by simp : u ∈ _)
    have hv := subset_convexHull ℝ {0, u, v} (by simp : v ∈ _)
    convert convex_convexHull ℝ _ hu hv (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num) using 1
    norm_num [u, v]
  have hinterior : ((1 / 4, 3 / 4) : ℝ × ℝ) ∈ interior (latticeParallelogram u v) := by
    refine interior_maximal (t := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
      ?_ (isOpen_Ioo.prod isOpen_Ioo) ?_
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact ⟨x, y, hx.1.le, hx.2.le, hy.1.le, hy.2.le, by simp [u, v]⟩
    · norm_num [Set.mem_prod, Set.mem_Ioo]
  have h := (antidiagonal_triangle_bijOn huv).mapsTo ⟨htriangle, hinterior⟩
  convert h using 1 <;> norm_num [u, v]
