/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple polygons: definitions
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Simple polygons: definitions

A simple polygon has vertices `v₀, …, v_{n-1}` (`n ≥ 3`) in the real plane whose edges
`[vᵢ, vᵢ₊₁]` (indices mod `n`, `edge`) are nondegenerate and meet only at the common vertex of
consecutive edges (`IsSimplePolygon`). These are the definitions that the statements of
`WantedExt.Geometry.SegmentVisibilityShared`, and of the wanted modules built on it, use, moved
here unchanged (names included) so that their proofs can import them.

Source: S. K. Ghosh and P. P. Goswami, *Unsolved problems in visibility graphs of points, segments
and polygons* (arXiv:1012.5187), Section 2.
-/

@[expose] public section

namespace MathlibExt.Geometry.SegmentVisibilityShared

/-- The edge `[vᵢ, vᵢ₊₁]` of a polygon (indices mod `n`). -/
def edge {n : ℕ} (v : Fin n → ℝ × ℝ) (i : Fin n) : Set (ℝ × ℝ) :=
  segment ℝ (v i) (v (finRotate n i))

/-- `v` is a simple polygon: at least three vertices, nondegenerate edges, and edges meeting only at
the common vertex of consecutive edges. -/
def IsSimplePolygon {n : ℕ} (v : Fin n → ℝ × ℝ) : Prop :=
  3 ≤ n ∧ (∀ i, v i ≠ v (finRotate n i)) ∧
    ∀ i j, i ≠ j →
      (j = finRotate n i → edge v i ∩ edge v j = {v j}) ∧
      (i = finRotate n j → edge v i ∩ edge v j = {v i}) ∧
      (j ≠ finRotate n i → i ≠ finRotate n j → Disjoint (edge v i) (edge v j))

end MathlibExt.Geometry.SegmentVisibilityShared
