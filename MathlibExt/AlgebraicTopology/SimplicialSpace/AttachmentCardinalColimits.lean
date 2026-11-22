/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
public import MathlibExt.CategoryTheory.SmallObject.ConstructionComparison
public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentCardinalColimits
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

/-!
# Accessibility of simplicial-space cell attachment

For a monomorphic generating family eligible for the small object argument at a regular cardinal
κ with a chosen ordinal bottom, the one-step attachment functor on arrows preserves μ-filtered
colimits when μ is regular and both endpoints of every generator are μ-presentable. The result
concerns the full attachment functor at the specified family and cardinal.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace SimplicialSpace
variable (M : MorphismProperty SimplicialSpace.{u}) (κ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [M.IsCardinalForSmallObjectArgument κ] [∀ i : M.toSet, Mono (M.homFamily i)]

section Cardinal
variable (μ : Cardinal.{u}) [Fact μ.IsRegular]
    [∀ i : M.toSet, IsCardinalPresentable.{u} i.1.left μ]
    [∀ i : M.toSet, IsCardinalPresentable.{u} i.1.right μ]

/-- Both original endpoints supply the actual whole-Arrow μ-colimit preservation. -/
theorem originalAttachment_isCardinalAccessible :
    letI : HasPushouts SimplicialSpace.{u} := SmallObject.hasPushouts M κ
    letI : ∀ {X S : SimplicialSpace.{u}} (p : X ⟶ S),
        HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex M.homFamily p))
            SimplicialSpace.{u} :=
      fun {_ _} p => SmallObject.hasColimitsOfShape_discrete M κ _ _ p
    (SmallObject.functor M.homFamily).IsCardinalAccessible μ := by
  let _ : HasPushouts SimplicialSpace.{u} := SmallObject.hasPushouts M κ
  let _ : ∀ {X S : SimplicialSpace.{u}} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex M.homFamily p))
          SimplicialSpace.{u} :=
    fun {_ _} p => SmallObject.hasColimitsOfShape_discrete M κ _ _ p
  let _ : MorphismProperty.IsSmall.{u} M := SmallObject.isSmall M κ
  let _ : LocallySmall.{u} SimplicialSpace.{u} := SmallObject.locallySmall M κ
  let E : SimplicialSpace.{u} ≌
      ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) :=
    (SimplicialSpace.equivalenceSimplicialObject.{u}.trans
      (Functor.currying.trans
        ((prodOpEquiv (C := SimplexCategory) (D := SimplexCategory)).symm.congrLeft)))
  let F := E.functor
  let _ : F.IsEquivalence := E.isEquivalence_functor
  let _ : E.inverse.IsEquivalence := E.isEquivalence_inverse
  let _ : E.inverse.IsCardinalAccessible μ := inferInstance
  let jF := fun i : M.toSet => F.map (M.homFamily i)
  let _ : ∀ {X S : ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u)} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex jF p))
          ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) :=
    fun {_ _} _ => inferInstance
  let G := SmallObject.functor M.homFamily
  let H := SmallObject.functor jF
  let _ (i : M.toSet) : Mono (jF i) := inferInstance
  let _ (i : M.toSet) : IsCardinalPresentable.{u} (F.obj i.1.left) μ :=
    E.toAdjunction.isCardinalPresentable_leftAdjoint_obj μ i.1.left
  let _ (i : M.toSet) : IsCardinalPresentable.{u} (F.obj i.1.right) μ :=
    E.toAdjunction.isCardinalPresentable_leftAdjoint_obj μ i.1.right
  let _ : H.IsCardinalAccessible μ :=
    SmallObject.presheafAttachment_isCardinalAccessible
      (D := SimplexCategory × SimplexCategory) jF μ
  let _ : (F.mapArrow ⋙ H).IsCardinalAccessible μ := inferInstance
  let _ : (G ⋙ F.mapArrow).IsCardinalAccessible μ :=
    Functor.isCardinalAccessible_of_natIso
      (SmallObject.functorMapIso M.homFamily F).symm μ
  refine { preservesColimitOfShape := fun J _ _ => ?_ }
  let _ : PreservesColimitsOfShape J (G ⋙ F.mapArrow) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible (G ⋙ F.mapArrow) μ J
  exact preservesColimitsOfShape_of_reflects_of_preserves G F.mapArrow


end Cardinal
end SimplicialSpace
