/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalNaiveFibrations

/-!
# Public use of the finite-interval naive predicates

Concrete membership gives full prescribed diagonals against auxiliary
anodyne maps and both actual endpoint corners. The naive object predicate
uses the accepted generic extension API directly, without a duplicate
concrete extension theorem in production.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SSet.joyalInterval
open scoped Simplicial

universe u

namespace FiniteJoyalIntervalNaiveFibrationsTest

example (X : SSet.{u}) :
    auxiliaryNaiveFibrantObjects X ↔ auxiliaryNaiveFibrations (terminal.from X) := Iff.rfl

/-- The concrete naive right class supplies a full auxiliary anodyne diagonal. -/
lemma exists_anodyne_lift {A B X Y : SSet.{u}} {i : A ⟶ B}
    (hi : auxiliaryAnodyneExtensions i) (p : X ⟶ Y) (hp : auxiliaryNaiveFibrations p)
    {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have h : HasLiftingProperty i p := hp i hi
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The accepted generic extension criterion applies to the actual finite system. -/
lemma exists_extension {A B X : SSet.{u}} (hX : auxiliaryNaiveFibrantObjects X)
    (i : A ⟶ B) (hi : auxiliaryAnodyneExtensions i) (a : A ⟶ X) :
    ∃ l : B ⟶ X, i ≫ l = a :=
  (auxiliaryAnodyneExtensions.naiveFibrantObjects_iff_extensions X).1 hX i hi a

/-- Both actual generator corners have full prescribed diagonals in every dimension. -/
lemma exists_endpointCorner_lift {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryNaiveFibrations p) (n : ℕ) (ε : Fin 2)
    {a : pushout (SSet.boundary.{u} n).ι
      ((productPrecylinder.{u}.app (SSet.boundary.{u} n : SSet)).endpoint ε) ⟶ X}
    {b : productPrecylinder.{u}.I.obj (Δ[n] : SSet) ⟶ Y}
    (sq : CommSq a (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε) p b) :
    ∃ l : productPrecylinder.{u}.I.obj (Δ[n] : SSet) ⟶ X,
      productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε ≫ l = a ∧ l ≫ p = b := by
  have hp' : auxiliaryGenerators.rlp p := by
    simpa only [auxiliaryNaiveFibrations_eq_generatorRlp] using hp
  have h : HasLiftingProperty (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε) p :=
    hp' _ (auxiliaryGenerators.endpointCorner_mem n ε)
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end FiniteJoyalIntervalNaiveFibrationsTest
