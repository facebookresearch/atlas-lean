/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHom
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerHornReplacement

/-!
# The same original pointed inner-horn replacement

The canonical actual inner-horn functor acts on the entire original
boundary map and every full Under arrow. Its same original unit is
pointed, inner anodyne and categorical weak. Its full original output
is a quasicategory, with no assumed mapping comparison.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The canonical original inner-horn functor applied to the whole original endpoint boundary. -/
def replacementFunctor : Category.{u} ⥤ Category.{u} where
  obj X := Under.mk (X.hom ≫ SSet.innerHornReplacementUnit.app X.right)
  map {X Y} f := Under.homMk (SSet.innerHornReplacement.map f.right) (by
    change (X.hom ≫ SSet.innerHornReplacementUnit.app X.right) ≫
      SSet.innerHornReplacement.map f.right = Y.hom ≫ SSet.innerHornReplacementUnit.app Y.right
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => X.hom ≫ h) (SSet.innerHornReplacementUnit_naturality f.right)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun h => h ≫ SSet.innerHornReplacementUnit.app Y.right) (Under.w f)))))
  map_id X := by
    apply Under.UnderMorphism.ext
    exact SSet.innerHornReplacement.map_id X.right
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact SSet.innerHornReplacement.map_comp f.right g.right

/-- The same original canonical inner-horn unit retains the entire pointed boundary. -/
def replacementUnit : 𝟭 Category.{u} ⟶ replacementFunctor where
  app X := Under.homMk (SSet.innerHornReplacementUnit.app X.right) rfl
  naturality X Y f := by
    apply Under.UnderMorphism.ext
    exact SSet.innerHornReplacementUnit.naturality f.right

/-- Every whole original pointed replacement has its genuine quasicategory carrier. -/
theorem replacement_quasicategory (X : Category.{u}) :
    SSet.Quasicategory (replacementFunctor.obj X).right :=
  SSet.innerHornReplacement_quasicategory X.right

/-- The same original full pointed unit is genuinely inner anodyne. -/
theorem replacementUnit_innerAnodyne (X : Category.{u}) :
    SSet.innerAnodyneExtensions (replacementUnit.app X).right :=
  SSet.innerHornReplacementUnit_innerAnodyne X.right

/-- The same original full pointed unit is categorical weak. -/
theorem replacementUnit_categorical (X : Category.{u}) :
    SSet.categoricalEquivalences (replacementUnit.app X).right :=
  SSet.innerHornReplacementUnit_categorical X.right

/-- The same original whole coherent Hom unit is weak by the genuine original Quillen preservation. -/
theorem replacementUnit_hom_weak (X : Category.{u}) :
    SSet.realizationWeakEquivalences (homMap (replacementUnit.app X)) :=
  homMap_weak _ (replacementUnit_categorical X)

end CategoryTheory.CoherentRealization.OriginalPointed
