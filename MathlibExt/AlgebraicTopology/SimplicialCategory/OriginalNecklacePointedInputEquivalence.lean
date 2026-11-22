/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklacePointedFullyFaithful

/-!
# The same entire native input category as original pointed costructured arrows

Both inverse functors retain the complete original native necklace and
its entire original input map. Every original arrow over the source is
retained. The original category is not restricted by coefficients,
flags, fibrancy or any desired comparison property.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

open SSet.OriginalNecklace

/-- Every same whole original native input has its literal original pointed costructured arrow. -/
def toPointedInput (K : SSet.{u}) (x y : K _⦋0⦌) :
    Object K x y ⥤ CostructuredArrow pointedNativeFunctor.{u} (Under.mk (SSet.boundaryOneMap x y)) where
  obj T := CostructuredArrow.mk (pointedInputMap T)
  map f := CostructuredArrow.homMk f.necklaceMap (Under.UnderMorphism.ext f.over)
  map_id T := by apply CostructuredArrow.hom_ext; rfl
  map_comp f g := by apply CostructuredArrow.hom_ext; rfl

/-- Every whole original pointed input retains the original native input object and both literal vertex equations. -/
def fromPointedInput (K : SSet.{u}) (x y : K _⦋0⦌) :
    CostructuredArrow pointedNativeFunctor.{u} (Under.mk (SSet.boundaryOneMap x y)) ⥤ Object K x y where
  obj T :=
    { necklace := T.left
      input := T.hom.right
      source_eq := by
        have h := congrArg (fun f => SSet.boundary.ι (1 : Fin 2) ≫ f) (Under.w T.hom)
        have he : SSet.const (OriginalNecklaceHom.sourceVertex T.left) ≫ T.hom.right = SSet.const x :=
          (congrArg (fun f => f ≫ T.hom.right) (SSet.boundary_ι_one_boundaryOneMap
            (OriginalNecklaceHom.sourceVertex T.left) (OriginalNecklaceHom.targetVertex T.left))).symm.trans
              ((Category.assoc _ _ _).trans (h.trans (SSet.boundary_ι_one_boundaryOneMap x y)))
        have hs : SSet.const (OriginalNecklaceHom.sourceVertex T.left) = T.left.source :=
          (SSet.yonedaEquiv_symm_zero (OriginalNecklaceHom.sourceVertex T.left)).symm.trans
            (Equiv.symm_apply_apply SSet.yonedaEquiv T.left.source)
        exact (congrArg SSet.yonedaEquiv ((congrArg (fun f => f ≫ T.hom.right) hs).symm.trans he)).trans
          (SSet.yonedaEquiv_const x)
      target_eq := by
        have h := congrArg (fun f => SSet.boundary.ι (0 : Fin 2) ≫ f) (Under.w T.hom)
        have he : SSet.const (OriginalNecklaceHom.targetVertex T.left) ≫ T.hom.right = SSet.const y :=
          (congrArg (fun f => f ≫ T.hom.right) (SSet.boundary_ι_zero_boundaryOneMap
            (OriginalNecklaceHom.sourceVertex T.left) (OriginalNecklaceHom.targetVertex T.left))).symm.trans
              ((Category.assoc _ _ _).trans (h.trans (SSet.boundary_ι_zero_boundaryOneMap x y)))
        have hs : SSet.const (OriginalNecklaceHom.targetVertex T.left) = T.left.target :=
          (SSet.yonedaEquiv_symm_zero (OriginalNecklaceHom.targetVertex T.left)).symm.trans
            (Equiv.symm_apply_apply SSet.yonedaEquiv T.left.target)
        exact (congrArg SSet.yonedaEquiv ((congrArg (fun f => f ≫ T.hom.right) hs).symm.trans he)).trans
          (SSet.yonedaEquiv_const y) }
  map f := ⟨f.left, congrArg Under.Hom.right (CostructuredArrow.w f)⟩
  map_id T := Hom.ext rfl
  map_comp f g := Hom.ext rfl

/-- Both full original input functors are exact inverse presentations of the same entire native category. -/
def pointedInputEquivalence (K : SSet.{u}) (x y : K _⦋0⦌) :
    Object K x y ≌ CostructuredArrow pointedNativeFunctor.{u} (Under.mk (SSet.boundaryOneMap x y)) where
  functor := toPointedInput K x y
  inverse := fromPointedInput K x y
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
