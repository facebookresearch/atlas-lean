/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex

/-!
# Rows and transpose of a bisimplicial set

Transposing a simplicial object in simplicial sets exchanges its two simplex
variables.  On diagonal objects this gives a canonical isomorphism whose
components are literally identities: the two diagonal structure maps differ
only by the naturality square between the inner and outer maps.

Every outer degeneracy is a split monomorphism.  Consequently its geometric
realization is a closed T1 embedding.  This is only the separation-theoretic
shadow needed by later skeletal filtrations; no properness, weak-equivalence,
or diagonal-invariance claim is made here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite Simplicial

universe v u

namespace SSet

/-- Exchange the two simplex variables of a bisimplicial set. -/
def simplicialTransposeFunctor :
    SimplicialObject SSet.{u} ⥤ SimplicialObject SSet.{u} :=
  CategoryTheory.SimplicialObject.transposeFunctor (Type u)

/-- The row obtained by fixing the original inner simplicial degree. -/
abbrev simplicialRow (X : SimplicialObject SSet.{u})
    (a : SimplexCategoryᵒᵖ) : SSet.{u} :=
  (simplicialTransposeFunctor.obj X).obj a

@[simp]
theorem simplicialTransposeFunctor_obj_obj
    (X : SimplicialObject SSet.{u})
    (a b : SimplexCategoryᵒᵖ) :
    ((simplicialTransposeFunctor.obj X).obj a).obj b =
      (X.obj b).obj a :=
  CategoryTheory.SimplicialObject.transposeFunctor_obj_obj
    (Type u) X a b

@[simp]
theorem simplicialRow_obj (X : SimplicialObject SSet.{u})
    (a b : SimplexCategoryᵒᵖ) :
    (simplicialRow X a).obj b = (X.obj b).obj a :=
  rfl

@[simp]
theorem simplicialRow_map (X : SimplicialObject SSet.{u})
    (a : SimplexCategoryᵒᵖ) {b c : SimplexCategoryᵒᵖ} (k : b ⟶ c) :
    (simplicialRow X a).map k = (X.map k).app a :=
  rfl

@[simp]
theorem simplicialTranspose_map_app
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (a b : SimplexCategoryᵒᵖ) :
    ((simplicialTransposeFunctor.map η).app a).app b =
      (η.app b).app a :=
  CategoryTheory.SimplicialObject.transposeFunctor_map_app
    (Type u) η a b

/-- A transposed diagonal map first moves in the original outer direction and
then in the original inner direction. -/
@[simp]
theorem simplicialDiagonalTranspose_obj_map
    (X : SimplicialObject SSet.{u})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (simplicialDiagonalFunctor.obj
      (simplicialTransposeFunctor.obj X)).map f =
        (X.map f).app a ≫ (X.obj b).map f :=
  CategoryTheory.SimplicialObject.diagonalTranspose_obj_map
    (Type u) X f

/-- Transposing a bisimplicial set does not change its bisimplices on the
diagonal.  Naturality of the identity components is the commuting square
between the inner and outer actions. -/
def simplicialDiagonalTransposeIso (X : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (simplicialTransposeFunctor.obj X) ≅
      simplicialDiagonalFunctor.obj X :=
  CategoryTheory.SimplicialObject.diagonalTransposeIso (Type u) X

@[simp]
theorem simplicialDiagonalTransposeIso_hom_app
    (X : SimplicialObject SSet.{u}) (a : SimplexCategoryᵒᵖ) :
    (simplicialDiagonalTransposeIso X).hom.app a = 𝟙 _ :=
  CategoryTheory.SimplicialObject.diagonalTransposeIso_hom_app
    (Type u) X a

@[simp]
theorem simplicialDiagonalTransposeIso_inv_app
    (X : SimplicialObject SSet.{u}) (a : SimplexCategoryᵒᵖ) :
    (simplicialDiagonalTransposeIso X).inv.app a = 𝟙 _ :=
  CategoryTheory.SimplicialObject.diagonalTransposeIso_inv_app
    (Type u) X a

/-- The diagonal transpose isomorphism is natural in maps of bisimplicial
sets. -/
@[reassoc]
theorem simplicialDiagonalTransposeIso_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) :
    simplicialDiagonalFunctor.map (simplicialTransposeFunctor.map η) ≫
        (simplicialDiagonalTransposeIso Y).hom =
      (simplicialDiagonalTransposeIso X).hom ≫
        simplicialDiagonalFunctor.map η := by
  exact CategoryTheory.SimplicialObject.diagonalTransposeIso_naturality
    (Type u) η

end SSet

namespace CategoryTheory.SimplicialObject

/-- Every degeneracy of a simplicial object is a split monomorphism. -/
theorem mono_sigma {C : Type u} [Category.{v} C]
    (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    Mono (X.σ i) := by
  exact
    ({ retraction := X.δ i.castSucc
       id := X.δ_comp_σ_self } : SplitMono (X.σ i)).mono

end CategoryTheory.SimplicialObject

namespace SSet

/-- The realization of an outer degeneracy of a bisimplicial set is a closed
T1 embedding.  This does not assert a cofibration or any properness result. -/
theorem closedT1_rowDegeneracy (X : SimplicialObject SSet.{0})
    {n : ℕ} (i : Fin (n + 1)) :
    TopCat.closedT1Embeddings (SSet.toTop.map (X.σ i)) := by
  exact @SSet.closedT1Embeddings_toTop_map_of_mono _ _ (X.σ i)
    (SimplicialObject.mono_sigma X i)

end SSet

end
