/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.BoundaryProductFace

/-!
# Boundary product face cover client

Minimal direct-import client for `BoundaryProductFace`. Checks the boundary face cover
and the product face cover, with a thin restatement of the product cover. No claim is
made about general product preservation, and
`N = 0, 1` are left to that later packet. This gives no filling, anodyne, retract,
or model-category result.
-/

@[expose] public section

open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.BoundaryProductFaceTests

example (n : ℕ) (x : SSet.toTop.obj (SSet.boundary (n + 1))) :
    ∃ (i : Fin (n + 2))
      (p : SSet.toTop.obj (SSet.stdSimplex.face (n := n + 1) {i}ᶜ : SSet)),
      SSet.toTop.map
        (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)) p = x :=
  SSet.boundaryProductFace.exists_face_cover n x

example (n m : ℕ)
    (x : ↑(SSet.toTop.obj (SSet.boundary (n + 1)) ⨯
      SSet.toTop.obj (Δ[m] : SSet.{0}))) :
    ∃ (i : Fin (n + 2))
      (p : ↑(SSet.toTop.obj (SSet.stdSimplex.face (n := n + 1) {i}ᶜ : SSet) ⨯
        SSet.toTop.obj (Δ[m] : SSet.{0}))),
      (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.prod.map
        (SSet.toTop.map
          (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)))
        (CategoryTheory.CategoryStruct.id (SSet.toTop.obj (Δ[m] : SSet.{0}))))) p = x :=
  SSet.boundaryProductFace.exists_face_cover_prod n m x

theorem exists_face_cover_prod_client (n m : ℕ)
    (x : ↑(SSet.toTop.obj (SSet.boundary (n + 1)) ⨯
      SSet.toTop.obj (Δ[m] : SSet.{0}))) :
    ∃ (i : Fin (n + 2))
      (p : ↑(SSet.toTop.obj (SSet.stdSimplex.face (n := n + 1) {i}ᶜ : SSet) ⨯
        SSet.toTop.obj (Δ[m] : SSet.{0}))),
      (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.prod.map
        (SSet.toTop.map
          (SSet.Subcomplex.homOfLE (SSet.face_singleton_compl_le_boundary i)))
        (CategoryTheory.CategoryStruct.id (SSet.toTop.obj (Δ[m] : SSet.{0}))))) p = x :=
  SSet.boundaryProductFace.exists_face_cover_prod n m x

#print axioms exists_face_cover_prod_client
#print axioms SSet.boundaryProductFace.exists_face_cover_prod

end MathlibExtTest.AlgebraicTopology.ModelCategory.BoundaryProductFaceTests
