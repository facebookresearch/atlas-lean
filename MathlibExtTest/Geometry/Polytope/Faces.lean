/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Polytope.Faces

@[expose] public section

open MathlibExt.Geometry.Polytope

namespace MathlibExtTest.Geometry.Polytope.Faces

/-- Non-vacuity: the whole polytope is one of its faces. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset E) :
    convexHull ℝ (s : Set E) ∈ faces s :=
  IsExposed.refl _

/-- The faces of a polytope form a finite set, and each is spanned by points of `s`. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset E)
    (F : Set E) (hF : F ∈ faces s) :
    (faces s).Finite ∧ F = convexHull ℝ (F ∩ (s : Set E)) :=
  ⟨faces_finite s, eq_convexHull_inter_of_mem_faces hF⟩

/-- The face lattice of a polytope is finite, with the empty face at the bottom and the polytope
at the top. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset E) :
    Finite (FaceLattice s) ∧ (⊥ : FaceLattice s).1 = ∅ ∧
      (⊤ : FaceLattice s).1 = convexHull ℝ (s : Set E) :=
  ⟨inferInstance, FaceLattice.coe_bot, FaceLattice.coe_top⟩

/-- Faces of faces are faces; non-vacuity with `F` the polytope itself. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset E)
    (G : Set E) (hG : IsExposed ℝ (convexHull ℝ (s : Set E)) G) : G ∈ faces s :=
  mem_faces_of_isExposed (IsExposed.refl _) hG

end MathlibExtTest.Geometry.Polytope.Faces
