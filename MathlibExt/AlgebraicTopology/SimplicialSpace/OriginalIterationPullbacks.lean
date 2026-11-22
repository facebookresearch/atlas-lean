/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.Iteration.Pullbacks
public import MathlibExt.AlgebraicTopology.SimplicialSpace.AttachmentTransport
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
import MathlibExt.AlgebraicTopology.SimplicialSpace.Presheaf

/-!
# Pullback preservation by transfinite simplicial-space cell attachment

For a monomorphic family eligible for the small object argument at regular κ with a chosen
ordinal bottom, its κ-iteration on simplicial-space arrows preserves pullbacks and
monomorphisms. The transfinite construction uses the specified family, attachment transformation
and ordinal throughout.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SimplicialSpace

variable (M : MorphismProperty SimplicialSpace.{u}) (κ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [M.IsCardinalForSmallObjectArgument κ]
    [∀ i : M.toSet, Mono (M.homFamily i)]

/-- The exact original native κ-iteration; no raw SOA or new κ is selected. -/
theorem originalIteration_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (SmallObject.iteration M κ) := by
  let _ : HasPushouts SimplicialSpace.{u} := SmallObject.hasPushouts M κ
  let _ : ∀ {X S : SimplicialSpace.{u}} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex M.homFamily p))
        SimplicialSpace.{u} :=
    fun {_ _} p => SmallObject.hasColimitsOfShape_discrete M κ _ _ p
  let _ : HasIterationOfShape κ.ord.ToType SimplicialSpace.{u} :=
    SmallObject.hasIterationOfShape M κ
  let F := SimplicialSpace.toPresheaf.{u}
  let _ : F.IsEquivalence := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (SmallObject.functor M.homFamily) :=
    originalAttachment_preservesPullbacks M κ
  change PreservesLimitsOfShape WalkingCospan
    ((SmallObject.SuccStruct.ofNatTrans (SmallObject.ε M.homFamily)).iteration κ.ord.ToType)
  exact SmallObject.SuccStruct.arrow_iteration_preservesPullbacks_of_presheaf_equivalence
    F (SmallObject.ε M.homFamily)

/-- The native pullback consequence gives monicity without a second induction. -/
theorem originalIteration_preservesMonomorphisms :
    (SmallObject.iteration M κ).PreservesMonomorphisms := by
  let _ : PreservesLimitsOfShape WalkingCospan (SmallObject.iteration M κ) :=
    originalIteration_preservesPullbacks M κ
  infer_instance

end SimplicialSpace
