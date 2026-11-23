/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 37, Problem 2
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.CompletePartialOrder
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Geometry.AMR37Problem2Wanted

/-! Source record `UM-03800002-Q001`. -/
/-- Points of `ℝ³`. -/
abbrev Point3 := EuclideanSpace ℝ (Fin 3)

/-- The unit cube `[0, 1]³`. -/
def stdCube : Set Point3 :=
  {p | ∀ i : Fin 3, 0 ≤ (WithLp.ofLp p) i ∧ (WithLp.ofLp p) i ≤ 1}

/-- The component of `v` orthogonal to `e`. -/
noncomputable def vecOrth (e v : Point3) : Point3 :=
  v - (inner (𝕜 := ℝ) v e / inner (𝕜 := ℝ) e e) • e

/-- The closed tetrahedron spanned by four points. -/
def tetraHull (v : Fin 4 → Point3) : Set Point3 :=
  (convexHull ℝ) (Set.range v)

/-- A non-degenerate tetrahedron with all dihedral angles acute: for every edge `ab` and the other
two vertices `c`, `d`, the components of `c - b` and `d - b` orthogonal to `a - b` have positive
inner product. -/
def IsAcuteTetrahedron (v : Fin 4 → Point3) : Prop :=
  AffineIndependent ℝ v ∧
  ∀ (a b c d : Fin 4),
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      0 < inner (𝕜 := ℝ) (vecOrth (v a - v b) (v c - v b)) (vecOrth (v a - v b) (v d - v b))

/-- A triangulation of the cube by `n` non-degenerate tetrahedra with vertices in the cube: they
cover the cube, have disjoint interiors, and any two meet in a common (possibly empty) face. -/
def IsTriangulation (n : ℕ) (tetras : Fin n → Fin 4 → Point3) : Prop :=
  (∀ i, AffineIndependent ℝ (tetras i)) ∧
  (∀ i, ∀ p ∈ Set.range (tetras i), p ∈ stdCube) ∧
  (Set.iUnion (fun i => tetraHull (tetras i)) = stdCube) ∧
  (∀ i j, i ≠ j → Disjoint (interior (tetraHull (tetras i))) (interior (tetraHull (tetras j)))) ∧
  (∀ i j, i ≠ j → ∃ (s : Set (Fin 4)) (t : Set (Fin 4)),
      tetraHull (tetras i) ∩ tetraHull (tetras j) = (convexHull ℝ) ((tetras i) '' s) ∧
      tetraHull (tetras i) ∩ tetraHull (tetras j) = (convexHull ℝ) ((tetras j) '' t))

/-- The cube has a triangulation into tetrahedra whose dihedral angles are all acute. -/
def conjecture : Prop :=
  ∃ (n : ℕ) (tetras : Fin n → Fin 4 → Point3),
    IsTriangulation n tetras ∧ ∀ i, IsAcuteTetrahedron (tetras i)

-- Carried source audit `UM-03800002-Q001` (see the Moved/ record).

/--
Resolved true: Resolved affirmatively: Kopczyński, Pak and Przytycki (Acute triangulations of
polyhedra and R^n, Combinatorica 32 (2012), arXiv:0909.3706) construct a triangulation of the
3-cube into tetrahedra whose dihedral angles are all acute, and VanderZee, Hirani, Guoy and
Ramos (A dihedral acute triangulation of the cube, arXiv:0905.3715) give another. Source: E.
Kopczyński, I. Pak, P. Przytycki, Acute triangulations of polyhedra and R^n, Combinatorica 32
(2012), arXiv:0909.3706, https://arxiv.org/abs/0909.3706. Moved from
`OpenConjectures/Geometry/AMR37Problem2`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.AMR37Problem2Wanted
