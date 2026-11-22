/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCylinder

/-!
# Finite Joyal Interval Cylinder
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory HomotopicalAlgebra

universe u

namespace SSet.FiniteJoyalIntervalCylinderTest

/-- The actual object and projection of the native product precylinder. -/
theorem data (X : SSet.{u}) :
    joyalInterval.productPrecylinder.I.obj X = joyalInterval ⊗ X ∧
      (joyalInterval.productPrecylinder.app X).π = snd joyalInterval X :=
  ⟨rfl, joyalInterval.productPrecylinder_projection X⟩

/-- Either prescribed endpoint retracts through the actual projection. -/
theorem endpointRetraction (X : SSet.{u}) (ε : Fin 2) :
    (joyalInterval.productPrecylinder.app X).endpoint ε ≫
      (joyalInterval.productPrecylinder.app X).π = 𝟙 X :=
  (joyalInterval.productPrecylinder.app X).endpoint_π ε

/-- The public pullback result accepts every map without a mono premise. -/
theorem endpointPullback {X Y : SSet.{u}} (i : X ⟶ Y) (ε : Fin 2) :
    IsPullback i ((joyalInterval.productPrecylinder.app X).endpoint ε)
      ((joyalInterval.productPrecylinder.app Y).endpoint ε) (joyalInterval ◁ i) :=
  joyalInterval.productPrecylinder_endpoint_isPullback i ε

/-- Exactness sends an actual value-universe small colimit to a colimit. -/
noncomputable def mappedColimit {J : Type u} [Category.{u} J] (D : J ⥤ SSet.{u}) :
    IsColimit (joyalInterval.productPrecylinder.I.mapCocone (colimit.cocone D)) :=
  isColimitOfPreserves joyalInterval.productPrecylinder.I (colimit.isColimit D)

/-- The full product boundary has an actual diagonal against any mono-RLP map. -/
theorem boundaryLift {X Z B : SSet.{u}} (p : Z ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p)
    (a : X ⨿ X ⟶ Z) (b : joyalInterval ⊗ X ⟶ B)
    (sq : CommSq a (joyalInterval.productPrecylinder.app X).i p b) :
    ∃ l : joyalInterval ⊗ X ⟶ Z,
      (joyalInterval.productPrecylinder.app X).i ≫ l = a ∧ l ≫ p = b := by
  have h : HasLiftingProperty (joyalInterval.productPrecylinder.app X).i p :=
    hp _ (MorphismProperty.monomorphisms.infer_property _)
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SSet.FiniteJoyalIntervalCylinderTest
