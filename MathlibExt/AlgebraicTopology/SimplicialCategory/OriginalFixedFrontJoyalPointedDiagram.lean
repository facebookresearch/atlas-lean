/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontPointedAugmentation
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalSSet

/-!
# The SAME original pointed diagram on the named Joyal carrier

The existing Joyal carrier equivalence preserves the entire original
endpoint boundary, every original quotient object and all underlying
maps. It transfers the actual pointed fixed-front diagram and its
augmentation to the named carrier used by the genuine Joyal model.
No new model factory or resolution outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The original endpoint-fixed category on the SAME named Joyal carrier. -/
abbrev PointedJoyal := Under (JoyalSSet.ofSSet.{u}.obj (∂Δ[1] : SSet.{u}))

/-- The existing Joyal carrier designation retains both original boundary maps and all underlying arrows. -/
def pointedCopyFunctor : Under (∂Δ[1] : SSet.{u}) ⥤ PointedJoyal.{u} where
  obj X := Under.mk (JoyalSSet.ofSSet.map X.hom)
  map {X Y} f := by
    have h : JoyalSSet.ofSSet.map X.hom ≫ JoyalSSet.ofSSet.map f.right = JoyalSSet.ofSSet.map Y.hom :=
      (JoyalSSet.ofSSet.map_comp X.hom f.right).symm.trans (congrArg JoyalSSet.ofSSet.map (Under.w f))
    exact Under.homMk (JoyalSSet.ofSSet.map f.right) h
  map_id X := Under.UnderMorphism.ext (JoyalSSet.ofSSet.map_id X.right)
  map_comp f g := Under.UnderMorphism.ext (JoyalSSet.ofSSet.map_comp f.right g.right)

/-- Forgetting the designation retains the SAME entire original boundary and every underlying pointed map. -/
def pointedRawFunctor : PointedJoyal.{u} ⥤ Under (∂Δ[1] : SSet.{u}) where
  obj X := Under.mk (JoyalSSet.forget.map X.hom)
  map {X Y} f := by
    have h : JoyalSSet.forget.map X.hom ≫ JoyalSSet.forget.map f.right = JoyalSSet.forget.map Y.hom :=
      (JoyalSSet.forget.map_comp X.hom f.right).symm.trans (congrArg JoyalSSet.forget.map (Under.w f))
    exact Under.homMk (JoyalSSet.forget.map f.right) h
  map_id X := Under.UnderMorphism.ext (JoyalSSet.forget.map_id X.right)
  map_comp f g := Under.UnderMorphism.ext (JoyalSSet.forget.map_comp f.right g.right)

/-- The SAME original full fixed-front pointed diagram on the actual named Joyal model carrier. -/
def pointedJoyalDiagram : CosimplicialObject PointedJoyal.{u} :=
  pointedCosimplicialObject ⋙ pointedCopyFunctor

/-- The SAME actual constant-front pointed augmentation on the named Joyal carrier. -/
def pointedJoyalAugmentation :
    pointedJoyalDiagram.{u} ⟶ (Functor.const SimplexCategory).obj (pointedCopyFunctor.obj (pointedObject.{u} 0)) where
  app n := pointedCopyFunctor.map (pointedAugmentation.app n)
  naturality n m θ := by
    change pointedCopyFunctor.map (pointedMap θ) ≫
      pointedCopyFunctor.map (pointedAugmentation.app m) =
        pointedCopyFunctor.map (pointedAugmentation.app n) ≫ 𝟙 _
    exact (pointedCopyFunctor.map_comp _ _).symm.trans
      ((congrArg pointedCopyFunctor.map
        ((pointedAugmentation.naturality θ).trans (Category.comp_id _))).trans (Category.comp_id _).symm)

/-- The copied augmentation retains the SAME original complete constant-front quotient map. -/
theorem pointedJoyalAugmentation_right (n : SimplexCategory) :
    JoyalSSet.forget.map (pointedJoyalAugmentation.{u}.app n).right = toZero n.len := rfl

/-- The copied cosimplicial diagram retains the SAME entire original quotient diagram after forgetting the
designation. -/
theorem pointedJoyalDiagram_raw : pointedJoyalDiagram.{u} ⋙ pointedRawFunctor = pointedCosimplicialObject.{u} := rfl

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
