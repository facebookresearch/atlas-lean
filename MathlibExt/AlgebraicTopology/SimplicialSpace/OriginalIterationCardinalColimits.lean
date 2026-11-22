/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.AttachmentCardinalColimits
public import MathlibExt.CategoryTheory.SmallObject.Iteration.Accessible

/-!
# Accessibility of transfinite simplicial-space cell attachment

The κ-iteration of simplicial-space cell attachment preserves μ-filtered colimits for a
monomorphic family eligible at regular κ with a chosen ordinal bottom, provided μ is regular and
both endpoints of every generator are μ-presentable. Accessibility is proved for the specified
transfinite arrow functor and its original attachment transformation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace SimplicialSpace
variable (M : MorphismProperty SimplicialSpace.{u}) (κ μ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [M.IsCardinalForSmallObjectArgument κ] [Fact μ.IsRegular]
    [∀ i : M.toSet, Mono (M.homFamily i)]
    [∀ i : M.toSet, IsCardinalPresentable.{u} i.1.left μ]
    [∀ i : M.toSet, IsCardinalPresentable.{u} i.1.right μ]

/-- Existing generic iteration closure applies to the same original ε, κ and family. -/
theorem originalIteration_isCardinalAccessible :
    (SmallObject.iteration M κ).IsCardinalAccessible μ := by
  let _ : HasPushouts SimplicialSpace.{u} := SmallObject.hasPushouts M κ
  let _ : ∀ {X S : SimplicialSpace.{u}} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex M.homFamily p))
          SimplicialSpace.{u} :=
    fun {_ _} p => SmallObject.hasColimitsOfShape_discrete M κ _ _ p
  let _ : HasIterationOfShape κ.ord.ToType SimplicialSpace.{u} :=
      SmallObject.hasIterationOfShape M κ
  let _ : (SmallObject.functor M.homFamily).IsCardinalAccessible μ :=
    originalAttachment_isCardinalAccessible M κ μ
  change ((SmallObject.SuccStruct.ofNatTrans (SmallObject.ε M.homFamily)).iteration
    κ.ord.ToType).IsCardinalAccessible μ
  exact SmallObject.SuccStruct.isCardinalAccessible_iteration
    (J := κ.ord.ToType) (SmallObject.ε M.homFamily) μ

end SimplicialSpace
