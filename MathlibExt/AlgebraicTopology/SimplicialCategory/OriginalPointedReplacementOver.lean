/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedInnerHornReplacement
import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-!
# Full original pointed replacement over the same original target

A genuine original replacement retraction of the target extends every
whole input using the same canonical replacement functor. The original
unit supplies natural transformations from the identity to both
composites, retaining every original input map and boundary equation.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The same full original pointed replacement over a target with its actual original unit retraction. -/
def replacementOverFunctor (K : Category.{u}) (r : replacementFunctor.obj K ⟶ K) : Over K ⥤ Over K where
  obj X := Over.mk (replacementFunctor.map X.hom ≫ r)
  map {X Y} f := Over.homMk (replacementFunctor.map f.left) (by
    change (replacementFunctor.map f.left ≫ replacementFunctor.map Y.hom) ≫ r =
      replacementFunctor.map X.hom ≫ r
    exact congrArg (fun h => h ≫ r)
      ((replacementFunctor.map_comp f.left Y.hom).symm.trans
        (congrArg replacementFunctor.map (Over.w f))))
  map_id X := by
    apply Over.OverMorphism.ext
    exact replacementFunctor.map_id X.left
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact replacementFunctor.map_comp f.left g.left

/-- The original unit is a whole natural pointed replacement comparison over the same target. -/
def replacementOverUnit (K : Category.{u}) (r : replacementFunctor.obj K ⟶ K)
    (hr : replacementUnit.app K ≫ r = 𝟙 K) :
    𝟭 (Over K) ⟶ replacementOverFunctor K r where
  app X := Over.homMk (replacementUnit.app X.left) (by
    change replacementUnit.app X.left ≫ (replacementFunctor.map X.hom ≫ r) = X.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ r) (replacementUnit.naturality X.hom).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun h => X.hom ≫ h) hr).trans (Category.comp_id _)))))
  naturality X Y f := by
    apply Over.OverMorphism.ext
    exact replacementUnit.naturality f.left

/-- Every same full original replacement-over-target carrier is a genuine quasicategory. -/
theorem replacementOver_quasicategory (K : Category.{u}) (r : replacementFunctor.obj K ⟶ K)
    (X : Over K) :
    SSet.Quasicategory ((replacementOverFunctor K r).obj X).left.right :=
  replacement_quasicategory X.left

end CategoryTheory.CoherentRealization.OriginalPointed
