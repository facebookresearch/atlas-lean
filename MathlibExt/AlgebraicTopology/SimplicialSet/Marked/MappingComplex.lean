/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Actual marked standard-simplex mapping complexes

An n-simplex is a genuine marked map from the product of the original
minimally or maximally marked standard simplex and the original source.
The ordinary Yoneda functor supplies all simplicial restriction equations.
Pre- and postcomposition retain the same original marked maps. These are
carrier constructions; no Kan or marked-model theorem is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Which original standard-simplex edges are marked in a parameter object. -/
inductive ParameterMarking
  | minimal
  | maximal

/-- The original standard simplices with either genuine parameter marking. -/
def simplexParameter (k : ParameterMarking) : SimplexCategory ⥤ Marked.{u} :=
  match k with
  | .minimal => SSet.stdSimplex ⋙ Marked.minimal
  | .maximal => SSet.stdSimplex ⋙ Marked.maximal

/-- Product with the original marked source uses the same original product maps. -/
def prodRight (X : Marked.{u}) : Marked.{u} ⥤ Marked.{u} where
  obj A := prod A X
  map f := prodMap f (𝟙 X)
  map_id A := prodMap_id A X
  map_comp f g := by
    simpa only [Category.id_comp] using prodMap_comp f g (𝟙 X) (𝟙 X)

/-- A marked source map gives its original natural product map in the source coordinate. -/
def prodRightMap {X X' : Marked.{u}} (f : X ⟶ X') : prodRight X ⟶ prodRight X' where
  app A := prodMap (𝟙 A) f
  naturality _ _ _ := by
    apply Hom.ext
    ext n a
    rfl

/-- The actual marked mapping complex is the original standard-simplex restriction of Yoneda. -/
def mappingComplex (k : ParameterMarking) (X Y : Marked.{u}) : SSet.{u} :=
  (simplexParameter k ⋙ prodRight X).op ⋙ CategoryTheory.yoneda.obj Y

/-- A simplex is exactly its original marked parameter-product map. -/
def mappingComplexSimplexEquiv (k : ParameterMarking) (X Y : Marked.{u}) (n : ℕ) :
    (mappingComplex k X Y) _⦋n⦌ ≃ (prod ((simplexParameter k).obj ⦋n⦌) X ⟶ Y) :=
  Equiv.refl _

/-- Postcomposition is the original marked map in the target coordinate. -/
def mappingComplexPost (k : ParameterMarking) (X : Marked.{u}) {Y Z : Marked.{u}} (f : Y ⟶ Z) :
    mappingComplex k X Y ⟶ mappingComplex k X Z :=
  Functor.whiskerLeft (simplexParameter k ⋙ prodRight X).op (CategoryTheory.yoneda.map f)

/-- Precomposition retains the original source map and parameter coordinate literally. -/
def mappingComplexPre (k : ParameterMarking) {X X' : Marked.{u}} (f : X' ⟶ X) (Y : Marked.{u}) :
    mappingComplex k X Y ⟶ mappingComplex k X' Y :=
  Functor.whiskerRight (NatTrans.op (Functor.whiskerLeft (simplexParameter k) (prodRightMap f)))
    (CategoryTheory.yoneda.obj Y)

/-- The complete postcomposition simplex is the same original composition. -/
@[simp] theorem mappingComplexPost_app (k : ParameterMarking) (X : Marked.{u})
    {Y Z : Marked.{u}} (f : Y ⟶ Z) (n : ℕ) (g : (mappingComplex k X Y) _⦋n⦌) :
    (mappingComplexPost k X f).app (op ⦋n⦌) g = g ≫ f := rfl

/-- The complete precomposition simplex is the same original product followed by the map. -/
@[simp] theorem mappingComplexPre_app (k : ParameterMarking) {X X' : Marked.{u}}
    (f : X' ⟶ X) (Y : Marked.{u}) (n : ℕ) (g : (mappingComplex k X Y) _⦋n⦌) :
    (mappingComplexPre k f Y).app (op ⦋n⦌) g =
      prodMap (𝟙 ((simplexParameter k).obj ⦋n⦌)) f ≫ g := rfl

end SSet.Marked
