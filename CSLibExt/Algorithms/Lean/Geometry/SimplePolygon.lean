/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Simple polygon boundaries

This file defines simplicity for a cyclic sequence of vertices in the real plane. It concerns only
the boundary, not a filled region. Polygonal Jordan separation is a separate hypothesis for results
about the interior; it is not part of the definition.

## References

* M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and
  Applications*, 3rd ed., Springer, 2008.
* J. O'Rourke, *Computational Geometry in C*, 2nd ed., Cambridge University Press, 1998.
* D. M. Mount, *CMSC 754 Computational Geometry*, Fall 2021, Lecture 5 (polygon triangulation).
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Geometry

/-- A cyclic sequence `v` of `n` points in the real plane forms a simple polygon boundary if
`n ≥ 3`, the vertices are pairwise distinct, and the closed edges satisfy the following conditions:
consecutive edges intersect in exactly their shared endpoint, and distinct nonconsecutive edges
are disjoint. The edge at index `i` joins `v i` to `v (finRotate n i)`, so the last edge closes at
vertex zero and is consecutive to the first edge. No orientation or strict convexity is required. -/
def IsSimplePolygon {n : ℕ} (v : Fin n → ℝ × ℝ) : Prop :=
  let edge (i : Fin n) := segment ℝ (v i) (v (finRotate n i))
  3 ≤ n ∧ Function.Injective v ∧
    (∀ i, edge i ∩ edge (finRotate n i) = {v (finRotate n i)}) ∧
    ∀ i j, i ≠ j → j ≠ finRotate n i → i ≠ finRotate n j → Disjoint (edge i) (edge j)

end Cslib.Algorithms.Lean.Geometry
