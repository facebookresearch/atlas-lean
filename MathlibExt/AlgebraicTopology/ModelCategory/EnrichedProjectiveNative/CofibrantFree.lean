/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Cofibrant free objects in the original native projective model

The chosen enriched free/evaluation adjunction supplies cofibrant free
objects at every original index and for every cofibrant coefficient. The
coefficient unit is proved cofibrant in the actual pointed-CGWH model.
No native spectrum smash, sphere identification, stable model or unit
axiom is an input. The original realized cardinal and caller's bottom
remain the ones of the existing native model.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- Each true cofibrant coefficient gives a cofibrant object of the same
native projective model under its original enriched Free functor. -/
theorem freeAt_obj_isCofibrant (a : A) (X : PointedCGWH.{u, v}) [IsCofibrant X] :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    IsCofibrant ((EnrichedFunctorCat.Free.functor a).obj X) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
  let _ : Adjunction.IsQuillenAdjunction
      (EnrichedFunctorCat.Free.adjunction (V := PointedCGWH.{u, v}) a) :=
    freeAtEvaluation_isQuillenAdjunction a
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := EnrichedFunctorCat.Free.adjunction a) inferInstance

/-- The actual scalar smash unit gives a cofibrant free object at every
original enriched index, with no sphere-Free comparison assumed. -/
theorem freeAt_unit_isCofibrant (a : A) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    IsCofibrant ((EnrichedFunctorCat.Free.functor a).obj (𝟙_ PointedCGWH.{u, v})) := by
  let _ : IsCofibrant (𝟙_ PointedCGWH.{u, v}) :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant
  exact freeAt_obj_isCofibrant a (𝟙_ PointedCGWH.{u, v})

/-- The same actual Free functor sends every coefficient cofibration to a
cofibration of the unchanged native model. -/
theorem freeAt_map_mem_cofibrations
    (a : A) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : cofibrations PointedCGWH.{u, v} f) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      ((EnrichedFunctorCat.Free.functor a).map f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
  exact (freeAtEvaluation_isQuillenAdjunction a).preservesCofibrations f hf

/-- Every original coefficient trivial cofibration is sent to an actual
native projective trivial cofibration by the same Free functor. -/
theorem freeAt_map_mem_trivialCofibrations
    (a : A) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : trivialCofibrations PointedCGWH.{u, v} f) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      ((EnrichedFunctorCat.Free.functor a).map f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
  exact (freeAtEvaluation_isQuillenAdjunction a).preservesTrivialCofibrations f hf

/-- The literal image of the scalar initial unit map is a native
cofibration. Its source is the original Free of the scalar initial object. -/
theorem freeAt_initial_unit_map_mem_cofibrations (a : A) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := modelCategory
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      ((EnrichedFunctorCat.Free.functor a).map (initial.to (𝟙_ PointedCGWH.{u, v}))) := by
  let _ : IsCofibrant (𝟙_ PointedCGWH.{u, v}) :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant
  exact freeAt_map_mem_cofibrations a _ ((cofibration_iff _).mp inferInstance)

omit B in
/-- The original free source of that initial-unit arrow is genuinely
initial by the actual chosen adjunction, rather than an assumed objectwise
zero or sphere presentation. -/
noncomputable def freeAtInitialIsInitial (a : A) :
    IsInitial ((EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v}) a).obj
      (⊥_ PointedCGWH.{u, v})) := by
  let _ : PreservesColimitsOfSize.{0, 0}
      (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v}) a) :=
    (EnrichedFunctorCat.Free.adjunction a).leftAdjoint_preservesColimits
  exact IsInitial.isInitialObj (EnrichedFunctorCat.Free.functor a) _ initialIsInitial

/-- Deprecated alias for `freeAtInitialIsInitial`. -/
@[deprecated freeAtInitialIsInitial (since := "2026-10-28"), nolint defsWithUnderscore]
alias freeAt_initial_isInitial := freeAtInitialIsInitial

omit B in
/-- At every original index the actual initial unit arrow is the literal
scalar initial map tensor the full original enriched Hom. -/
theorem freeAt_initial_unit_map_component (a b : A) :
    EnrichedFunctorCat.component
        ((EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v}) a).map
          (initial.to (𝟙_ PointedCGWH.{u, v}))) b =
      initial.to (𝟙_ PointedCGWH.{u, v}) ▷ (a ⟶[PointedCGWH.{u, v}] b) :=
  EnrichedFunctorCat.Free.coefficientMap_component _ _ _

end HomotopicalAlgebra.EnrichedProjective.Native
