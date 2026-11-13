/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-3385-015: Every C^∞-embedded two-sphere in R^3 contains six points
spanning a regular octahedron.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Batteries.Util.ProofWanted

@[expose] public section

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.InscribedRegularOctahedronWanted

/-! Source record `OWR-3385-015`. -/

/-- The unit two-sphere in three-dimensional space, as a manifold
(the subtype `Metric.sphere` in `EuclideanSpace ℝ (Fin 3)`). -/
abbrev Sphere2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Opposite vertex pairs of the octahedron, labelled `0..5` with opposite
pairs `(0,1)`, `(2,3)` and `(4,5)`. -/
def Opposite : Fin 6 → Fin 6 → Prop := fun i j =>
  (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
  (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
  (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)

/-- Six points span a regular octahedron of edge length `s`: adjacent pairs
sit at distance `s` and opposite pairs at distance `s * √2`. -/
def IsRegularOctahedron (p : Fin 6 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ i j : Fin 6, i ≠ j →
    (Opposite i j → dist (p i) (p j) = s * Real.sqrt 2) ∧
    (¬Opposite i j → dist (p i) (p j) = s)

/-- [OWR-3385-015] Every C^∞-embedded two-sphere in `R^3` contains six
points spanning a regular octahedron. The embedding hypothesis is
Mathlib's `Manifold.IsSmoothEmbedding` for the sphere manifold, which
includes the immersion condition. -/
def conjecture : Prop :=
  ∀ f : Sphere2 → EuclideanSpace ℝ (Fin 3),
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f →
      ∃ p : Fin 6 → EuclideanSpace ℝ (Fin 3),
        (∀ i, ∃ z : Sphere2, f z = p i) ∧ IsRegularOctahedron p

/--
Resolved true: Karasev (arXiv:0905.2671, 2009), Theorem 2 and Section 5, extending Makeev's
smooth convex case, proves that for odd prime powers d every smoothly embedded S^(d-1) in R^d
contains the vertices of a regular crosspolytope; d = 3 gives the regular octahedron (Matschke,
Trans. AMS 2022, Thm 5.1). Source: R. N. Karasev, Inscribing a regular crosspolytope, arXiv
preprint (2009), arXiv:0905.2671, https://arxiv.org/abs/0905.2671. Moved from
`OpenConjectures/Geometry/InscribedRegularOctahedron`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.InscribedRegularOctahedronWanted
