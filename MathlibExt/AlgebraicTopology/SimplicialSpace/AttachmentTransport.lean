/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
public import MathlibExt.CategoryTheory.SmallObject.ConstructionComparison
public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentPullbacks
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

/-!
# Pullback preservation by simplicial-space cell attachment

For a monomorphic generating family eligible for the small object argument at regular κ with a
chosen ordinal bottom, the one-step attachment functor on simplicial-space arrows preserves
pullbacks and monomorphisms. The pullback statement applies to arbitrary arrow spans and retains
the specified generating family.
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

/-- Pullbacks of every original Arrow span are preserved by the same one-step construction. -/
theorem originalAttachment_preservesPullbacks :
    letI : HasPushouts SimplicialSpace.{u} := SmallObject.hasPushouts M κ
    letI : ∀ {X S : SimplicialSpace.{u}} (p : X ⟶ S),
        HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex M.homFamily p))
            SimplicialSpace.{u} :=
      fun {_ _} p => SmallObject.hasColimitsOfShape_discrete M κ _ _ p
    PreservesLimitsOfShape WalkingCospan (SmallObject.functor M.homFamily) := by
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
  let jF := fun i : M.toSet => F.map (M.homFamily i)
  let _ : ∀ {X S : ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u)} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex jF p))
          ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) :=
    fun {_ _} _ => inferInstance
  let G := SmallObject.functor M.homFamily
  let H := SmallObject.functor jF
  let _ (i : M.toSet) : Mono (jF i) := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan H :=
    SmallObject.presheafAttachment_preservesPullbacks
      (D := SimplexCategory × SimplexCategory) jF
  let _ : PreservesLimitsOfShape WalkingCospan (F.mapArrow ⋙ H) := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (G ⋙ F.mapArrow) :=
    preservesLimitsOfShape_of_natIso
      (J := WalkingCospan) (SmallObject.functorMapIso M.homFamily F).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves G F.mapArrow

/-- Monicity of each original Arrow map is preserved; no span-monicity hypothesis is used. -/
theorem originalAttachment_preservesMonomorphisms :
    letI : HasPushouts SimplicialSpace.{u} := SmallObject.hasPushouts M κ
    letI : ∀ {X S : SimplicialSpace.{u}} (p : X ⟶ S),
        HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex M.homFamily p))
            SimplicialSpace.{u} :=
      fun {_ _} p => SmallObject.hasColimitsOfShape_discrete M κ _ _ p
    (SmallObject.functor M.homFamily).PreservesMonomorphisms := by
  let _ : HasPushouts SimplicialSpace.{u} := SmallObject.hasPushouts M κ
  let _ : ∀ {X S : SimplicialSpace.{u}} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex M.homFamily p))
          SimplicialSpace.{u} :=
    fun {_ _} p => SmallObject.hasColimitsOfShape_discrete M κ _ _ p
  let _ : PreservesLimitsOfShape WalkingCospan (SmallObject.functor M.homFamily) :=
    originalAttachment_preservesPullbacks M κ
  infer_instance

end SimplicialSpace
