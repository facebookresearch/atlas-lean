/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneClass

/-!
# Public clients for the auxiliary lifting closure

Raw generator right lifting supplies strict diagonals against every map
in the auxiliary anodyne class. Conversely, right lifting against that
class supplies both actual endpoint-corner diagonals in every dimension.
These clients use the public right-class identity and require no model
structure, quasicategory or monicity premise.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SSet.joyalInterval
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneClass

/-- The public right-class equality gives the full prescribed diagonal
against an arbitrary auxiliary anodyne map. -/
theorem exists_lift_of_generator_rlp {A B X Y : SSet.{u}} {i : A ⟶ B}
    (hi : auxiliaryAnodyneExtensions i) (p : X ⟶ Y) (hp : auxiliaryGenerators.rlp p)
    {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have hp' : auxiliaryAnodyneExtensions.rlp p := by
    rw [auxiliaryAnodyneExtensions.rlp_eq]
    exact hp
  have h : HasLiftingProperty i p := hp' i hi
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- In the reverse direction, class right lifting gives both original
specified corner lifts, including their zero-dimensional pushouts. -/
theorem exists_endpointCorner_lift {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryAnodyneExtensions.rlp p) (n : ℕ) (ε : Fin 2)
    {a : pushout (SSet.boundary.{u} n).ι
      ((productPrecylinder.{u}.app (SSet.boundary.{u} n : SSet)).endpoint ε) ⟶ X}
    {b : productPrecylinder.{u}.I.obj (Δ[n] : SSet) ⟶ Y}
    (sq : CommSq a (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε) p b) :
    ∃ l : productPrecylinder.{u}.I.obj (Δ[n] : SSet) ⟶ X,
      productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε ≫ l = a ∧ l ≫ p = b := by
  have hp' : auxiliaryGenerators.rlp p := by
    simpa only [auxiliaryAnodyneExtensions.rlp_eq] using hp
  have h : HasLiftingProperty (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε) p :=
    hp' _ (auxiliaryGenerators.endpointCorner_mem n ε)
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneClass
