/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Geometry.TriangleEdgeFunctions
import Mathlib.Tactic.NormNum

/-!
# Triangle edge-function tests

A translated triangle gives fixtures for a strict interior point, a point on an edge but not
in the interior, and a point outside the closed triangle.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

private noncomputable def a : ℝ × ℝ := (1, 1)
private noncomputable def b : ℝ × ℝ := (5, 1)
private noncomputable def c : ℝ × ℝ := (1, 5)

private theorem orientation : 0 < cross (b - a) (c - a) := by
  norm_num [a, b, c, cross, Prod.fst_sub, Prod.snd_sub]

-- All three directed edge values are positive.
example : ((2, 2) : ℝ × ℝ) ∈ interior (_root_.convexHull ℝ {a, b, c}) := by
  rw [(triangle_mem_iff_edge_signs a b c (2, 2) orientation).2]
  norm_num [a, b, c, cross, Prod.fst_sub, Prod.snd_sub]

-- The midpoint of `bc` belongs to the hull, but the `bc` edge value vanishes.
example : ((3, 3) : ℝ × ℝ) ∈ _root_.convexHull ℝ {a, b, c} ∧
    ((3, 3) : ℝ × ℝ) ∉ interior (_root_.convexHull ℝ {a, b, c}) := by
  have h := triangle_mem_iff_edge_signs a b c (3, 3) orientation
  rw [h.1, h.2]
  norm_num [a, b, c, cross, Prod.fst_sub, Prod.snd_sub]

-- The point across `ca` has negative `ca` edge value.
example : ((0, 2) : ℝ × ℝ) ∉ _root_.convexHull ℝ {a, b, c} := by
  rw [(triangle_mem_iff_edge_signs a b c (0, 2) orientation).1]
  norm_num [a, b, c, cross, Prod.fst_sub, Prod.snd_sub]

end Cslib.Algorithms.Lean.Geometry
