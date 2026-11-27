/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Polytope.BoundaryComplex
import MathlibExt.Geometry.Polytope.GaleEvenness
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open MathlibExt.Geometry.Polytope MathlibExt.Geometry.Polytope.FaceNumbersWanted
open MathlibExt.Combinatorics.SimplicialSphereShared

namespace MathlibExtTest.Geometry.Polytope.BoundaryComplex

-- An interior point belongs to none of the simplices of the boundary complex.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Finset E} (hsimp : IsSimplicial s) {x : E}
    (hx : x ∈ interior (convexHull ℝ (s : Set E))) :
    x ∉ (boundaryComplex (Set.nonempty_of_mem hx) hsimp).space := by
  rw [boundary_space]
  exact fun h => h.2 hx

-- A singleton in the zero-dimensional ambient space is full-dimensional.
example : Nonempty (FiniteSimplicialSphere 0) := by
  let s : Finset (EuclideanSpace ℝ (Fin 0)) := {0}
  have h : (s : Set (EuclideanSpace ℝ (Fin 0))) = Set.univ := by
    ext x
    simp [s, Subsingleton.elim x 0]
  have hs : IsSimplicial s := by
    intro F _ _ hd
    have hdim : dim s ≤ 0 := (Submodule.finrank_le _).trans_eq finrank_euclideanSpace_fin
    omega
  obtain ⟨X, -⟩ := exists_simplicialSphere_faceCount_eq s (by simp [h]) hs
  exact ⟨X⟩

-- The boundary of the triangle on three moment-curve points has three vertices and three edges.
example : ∃ X : FiniteSimplicialSphere 2, faceCount X 0 = 3 ∧ faceCount X 1 = 3 := by
  let t (i : Fin 3) : ℝ := i.val
  have ht : Function.Injective t := fun i j h => Fin.ext (Nat.cast_injective h)
  have hi := affineIndependent_momentCurve (d := 2) le_rfl ht
  have hspan := hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
  have hfull : (interior (cyclicPolytope 2 t)).Nonempty := by
    apply (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.mpr
    simpa [affineSpan_convexHull, cyclicVertices] using hspan
  obtain ⟨X, hX⟩ := exists_simplicialSphere_faceCount_eq _ hfull (isSimplicial_cyclicSimplex ht)
  exact ⟨X, (hX 0 (by decide)).trans (faceNumber_cyclicSimplex ht 0),
    (hX 1 (by decide)).trans (faceNumber_cyclicSimplex ht 1)⟩

end MathlibExtTest.Geometry.Polytope.BoundaryComplex
