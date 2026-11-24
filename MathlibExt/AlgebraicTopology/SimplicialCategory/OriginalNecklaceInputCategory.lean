/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceAllMaps

/-!
# The full original native necklace input category

Objects retain a whole original native necklace and its entire input
map at both supplied original vertices. All endpoint-preserving native
maps over that input are morphisms. No coefficient, flag, flanking,
fibrancy or comparison condition changes this original indexing category.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

open SSet.OriginalNecklace

/-- A whole original native necklace over the SAME original input and endpoints. -/
structure Object (K : SSet.{u}) (x y : K _⦋0⦌) where
  /-- The entire native necklace with every original joint and vertex. -/
  necklace : Data
  /-- The actual complete simplicial input map. -/
  input : necklace.object.{u} ⟶ K
  /-- The original source vertex is retained. -/
  source_eq : SSet.yonedaEquiv (necklace.source ≫ input) = x
  /-- The original target vertex is retained. -/
  target_eq : SSet.yonedaEquiv (necklace.target ≫ input) = y

variable {K : SSet.{u}} {x y : K _⦋0⦌}

/-- Every entire original native necklace map over the SAME supplied input. -/
structure Hom (T U : Object K x y) where
  /-- The actual endpoint-preserving full native map. -/
  necklaceMap : T.necklace ⟶ U.necklace
  /-- The whole original input square commutes. -/
  over : necklaceMap.map.{u} ≫ U.input = T.input

namespace Hom

/-- The original input-map morphism retains its exact native map without additional data. -/
@[ext]
theorem ext {T U : Object K x y} {f g : Hom T U} (h : f.necklaceMap = g.necklaceMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The same entire original identity over the input. -/
def id (T : Object K x y) : Hom T T where
  necklaceMap := 𝟙 T.necklace
  over := (congrArg (fun f => f ≫ T.input) (Morphism.map_id.{u} T.necklace)).trans (Category.id_comp _)

/-- The same entire original composition over the input. -/
def comp {T U V : Object K x y} (f : Hom T U) (g : Hom U V) : Hom T V where
  necklaceMap := f.necklaceMap ≫ g.necklaceMap
  over := (congrArg (fun h => h ≫ V.input) (Morphism.map_comp f.necklaceMap g.necklaceMap)).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun h => f.necklaceMap.map ≫ h) g.over).trans f.over))

end Hom

/-- The genuine full original necklace input category, retaining all original maps. -/
instance : Category (Object K x y) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.necklaceMap)
  comp_id f := Hom.ext (Category.comp_id f.necklaceMap)
  assoc f g h := Hom.ext (Category.assoc f.necklaceMap g.necklaceMap h.necklaceMap)

/-- The original indexing functor remembers the entire SAME native necklace. -/
def forget (K : SSet.{u}) (x y : K _⦋0⦌) : Object K x y ⥤ Data where
  obj T := T.necklace
  map f := f.necklaceMap

/-- All actual original input maps form the SAME natural transformation to the supplied input. -/
def inputTransformation (K : SSet.{u}) (x y : K _⦋0⦌) :
    forget K x y ⋙ SSet.OriginalNecklace.functor ⟶ (Functor.const (Object K x y)).obj K where
  app T := T.input
  naturality T U f := by
    change f.necklaceMap.map.{u} ≫ U.input = T.input ≫ 𝟙 K
    exact f.over.trans (Category.comp_id T.input).symm

/-- The whole original input transformation retains its SAME literal input component. -/
theorem inputTransformation_app (T : Object K x y) : (inputTransformation K x y).app T = T.input := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
