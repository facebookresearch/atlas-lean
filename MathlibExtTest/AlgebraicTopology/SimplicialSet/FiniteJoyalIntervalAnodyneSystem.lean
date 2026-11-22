/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem

/-!
# Public use of the auxiliary cylinder corner axioms

The native anodyne-system instance supplies full prescribed diagonals
against endpoint and boundary corners. The general product result applies
to arbitrary auxiliary anodyne maps and monomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MonoidalCategory SSet.joyalInterval

universe u

namespace FiniteJoyalIntervalAnodyneSystemTest

/-- Instance inference supplies all four genuine native anodyne-system fields. -/
example : productPrecylinder.{u}.IsAnodyneSystem.{u} auxiliaryAnodyneExtensions :=
  inferInstance

/-- The endpoint axiom preserves the entire prescribed pushout square. -/
lemma endpoint_lift {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i] (ε : Fin 2)
    (p : X ⟶ Y) (hp : auxiliaryNaiveFibrations p)
    {a : pushout i ((productPrecylinder.app A).endpoint ε) ⟶ X}
    {b : productPrecylinder.I.obj B ⟶ Y}
    (sq : CommSq a (productPrecylinder.endpointCorner i ε) p b) :
    ∃ l : productPrecylinder.I.obj B ⟶ X,
      productPrecylinder.endpointCorner i ε ≫ l = a ∧ l ≫ p = b := by
  have hi := Precylinder.IsAnodyneSystem.endpoint_corner
    (P := productPrecylinder) (An := auxiliaryAnodyneExtensions) i ε
  have h : HasLiftingProperty (productPrecylinder.endpointCorner i ε) p := hp _ hi
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The boundary axiom preserves both equations of a fully prescribed diagonal. -/
lemma boundary_lift {A B X Y : SSet.{u}} (i : A ⟶ B)
    (hi : auxiliaryAnodyneExtensions i) (p : X ⟶ Y) (hp : auxiliaryNaiveFibrations p)
    {a : pushout (coprod.map i i) (productPrecylinder.app A).i ⟶ X}
    {b : productPrecylinder.I.obj B ⟶ Y}
    (sq : CommSq a (productPrecylinder.boundaryCorner i) p b) :
    ∃ l : productPrecylinder.I.obj B ⟶ X,
      productPrecylinder.boundaryCorner i ≫ l = a ∧ l ≫ p = b := by
  have hAn := Precylinder.IsAnodyneSystem.boundary_corner
    (P := productPrecylinder) (An := auxiliaryAnodyneExtensions) i hi
  have h : HasLiftingProperty (productPrecylinder.boundaryCorner i) p := hp _ hAn
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Arbitrary anodyne and mono product corners retain actual lifting equations. -/
lemma product_lift {A B K L X Y : SSet.{u}} (i : A ⟶ B)
    (hi : auxiliaryAnodyneExtensions i) (j : K ⟶ L) [Mono j]
    (p : X ⟶ Y) (hp : auxiliaryNaiveFibrations p)
    {a : (Arrow.mk i □ Arrow.mk j).left ⟶ X} {b : B ⊗ L ⟶ Y}
    (sq : CommSq a (Arrow.mk i □ Arrow.mk j).hom p b) :
    ∃ l : B ⊗ L ⟶ X, (Arrow.mk i □ Arrow.mk j).hom ≫ l = a ∧ l ≫ p = b := by
  have hAn := auxiliaryAnodyneExtensions.pushoutProduct i hi j
  have h : HasLiftingProperty (Arrow.mk i □ Arrow.mk j).hom p := hp _ hAn
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end FiniteJoyalIntervalAnodyneSystemTest
