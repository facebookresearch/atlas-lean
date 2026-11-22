/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.VertexRestriction
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The whole original discrete-source coproduct mapping product

The actual parametrized tensor-Hom adjunction preserves the opposite
source limits. The original discrete embedding preserves coproducts.
Thus mapping from the entire original coproduct is the same native
product of both original mapping objects, with both restriction legs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u uI vI

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace

/-- The actual original discrete embedding preserves colimits of every supplied shape. -/
theorem discrete_preservesColimitsOfShape (I : Type uI) [Category.{vI} I]
    [∀ d : SimplexCategoryᵒᵖ, PreservesColimitsOfShape I
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj d)] :
    PreservesColimitsOfShape I SSet.simplicialSpaceDiscrete.{u} where
  preservesColimit {F} :=
    { preserves := fun {c} hc => ⟨by
      apply evaluationJointlyReflectsColimits _ (fun d => ?_)
      change IsColimit (((evaluation _ _).obj d ⋙ SimplicialObject.const (Type u)).mapCocone c)
      apply evaluationJointlyReflectsColimits _ (fun e => ?_)
      change IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj d).mapCocone c)
      exact isColimitOfPreserves _ hc⟩ }

/-- The actual original source mapping functor preserves every supplied limit shape in its source opposite. -/
theorem discreteSourceMapping_preservesLimitsOfShape
    (I : Type uI) [Category.{vI} I] (W : SimplicialSpace.{u})
    [∀ d : SimplexCategoryᵒᵖ, PreservesColimitsOfShape Iᵒᵖ
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj d)] :
    PreservesLimitsOfShape I (discreteSourceMapping W) := by
  let _ := discrete_preservesColimitsOfShape.{u} Iᵒᵖ
  let _ : PreservesColimitsOfShape Iᵒᵖ (SSet.simplicialSpaceDiscrete.{u} ⋙ ofSimplicialObject) := by
    infer_instance
  let _ : PreservesLimitsOfShape I (SSet.simplicialSpaceDiscrete.{u} ⋙ ofSimplicialObject).op :=
    preservesLimitsOfShape_op I _
  let _ : ∀ K : SSet.{u}, PreservesColimitsOfShape Iᵒᵖ
      (innerTensorBifunctor.flip.obj K) := fun K => by
    change PreservesColimitsOfShape Iᵒᵖ (innerTensor K)
    let _ : (innerTensor K).IsLeftAdjoint := (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  let _ : PreservesLimitsOfShape I (innerHomFunctor.flip.obj W) :=
    innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj I W
  change PreservesLimitsOfShape I
    ((SSet.simplicialSpaceDiscrete.{u} ⋙ ofSimplicialObject).op ⋙ innerHomFunctor.flip.obj W)
  infer_instance

private def oppositeCoprodFan (A B : SSet.{u}) : BinaryFan (op A) (op B) :=
  BinaryFan.mk (coprod.inl : A ⟶ A ⨿ B).op (coprod.inr : B ⟶ A ⨿ B).op

set_option backward.isDefEq.respectTransparency false in
private def oppositeCoprodIsLimit (A B : SSet.{u}) : IsLimit (oppositeCoprodFan A B) :=
  BinaryFan.IsLimit.mk _ (fun f g => (coprod.desc f.unop g.unop).op)
    (fun f g => Quiver.Hom.unop_inj (coprod.inl_desc _ _))
    (fun f g => Quiver.Hom.unop_inj (coprod.inr_desc _ _))
    (fun f g m hf hg => Quiver.Hom.unop_inj (by
      change m.unop = coprod.desc f.unop g.unop
      apply coprod.hom_ext
      · exact (congrArg Quiver.Hom.unop hf).trans (coprod.inl_desc _ _).symm
      · exact (congrArg Quiver.Hom.unop hg).trans (coprod.inr_desc _ _).symm))

private def coproductMappingIsLimit (W : SimplicialSpace.{u}) (A B : SSet.{u}) :
    IsLimit (BinaryFan.mk ((discreteSourceMapping W).map (coprod.inl : A ⟶ A ⨿ B).op)
      ((discreteSourceMapping W).map (coprod.inr : B ⟶ A ⨿ B).op)) := by
  let _ := discreteSourceMapping_preservesLimitsOfShape (Discrete WalkingPair) W
  exact mapIsLimitOfPreservesOfIsLimit (discreteSourceMapping W) _ _ (oppositeCoprodIsLimit A B)

set_option backward.isDefEq.respectTransparency false in
/-- The whole original coproduct maps naturally to the actual original product of both source mapping objects. -/
def discreteSourceCoproductIso (W : SimplicialSpace.{u}) (A B : SSet.{u}) :
    (discreteSourceMapping W).obj (op (A ⨿ B)) ≅
      (discreteSourceMapping W).obj (op A) ⨯ (discreteSourceMapping W).obj (op B) where
  hom := prod.lift ((discreteSourceMapping W).map (coprod.inl : A ⟶ A ⨿ B).op)
    ((discreteSourceMapping W).map (coprod.inr : B ⟶ A ⨿ B).op)
  inv := BinaryFan.IsLimit.lift (coproductMappingIsLimit W A B) prod.fst prod.snd
  hom_inv_id := by
    apply BinaryFan.IsLimit.hom_ext (coproductMappingIsLimit W A B)
    · simp only [Category.assoc, BinaryFan.IsLimit.lift_fst, prod.lift_fst, Category.id_comp]
      rfl
    · simp only [Category.assoc, BinaryFan.IsLimit.lift_snd, prod.lift_snd, Category.id_comp]
      rfl
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.id_comp]
      exact BinaryFan.IsLimit.lift_fst (coproductMappingIsLimit W A B) prod.fst prod.snd
    · rw [Category.assoc, prod.lift_snd, Category.id_comp]
      exact BinaryFan.IsLimit.lift_snd (coproductMappingIsLimit W A B) prod.fst prod.snd

/-- The whole forward source mapping comparison retains the original first coproduct restriction. -/
theorem discreteSourceCoproductIso_fst (W : SimplicialSpace.{u}) (A B : SSet.{u}) :
    (discreteSourceCoproductIso W A B).hom ≫ prod.fst =
      (discreteSourceMapping W).map (coprod.inl : A ⟶ A ⨿ B).op :=
  prod.lift_fst _ _

/-- The whole forward source mapping comparison retains the original second coproduct restriction. -/
theorem discreteSourceCoproductIso_snd (W : SimplicialSpace.{u}) (A B : SSet.{u}) :
    (discreteSourceCoproductIso W A B).hom ≫ prod.snd =
      (discreteSourceMapping W).map (coprod.inr : B ⟶ A ⨿ B).op :=
  prod.lift_snd _ _

end SimplicialSpace
