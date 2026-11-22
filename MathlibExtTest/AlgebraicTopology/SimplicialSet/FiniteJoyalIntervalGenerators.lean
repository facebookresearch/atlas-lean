/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGenerators

/-!
# Public clients for the finite-interval auxiliary family

Right lifting against the literal family gives actual diagonals against
inner horns and every endpoint corner. The canonical zero-dimensional arrow
isomorphism also gives actual interval-endpoint diagonals, without assuming
that an isomorphic representative is literally an `ofHoms` member.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SSet.joyalInterval
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGenerators

/-- A right lift against every literal generator supplies any inner-horn diagonal. -/
theorem exists_innerHorn_lift {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryGenerators.rlp p) {n : ℕ} {k : Fin (n + 1)}
    (h0 : 0 < k) (hn : k < Fin.last n)
    {a : (SSet.horn.{u} n k : SSet) ⟶ X} {b : (Δ[n] : SSet.{u}) ⟶ Y}
    (sq : CommSq a (SSet.horn n k).ι p b) :
    ∃ l : (Δ[n] : SSet.{u}) ⟶ X, (SSet.horn n k).ι ≫ l = a ∧ l ≫ p = b := by
  have h : HasLiftingProperty (SSet.horn n k).ι p :=
    hp _ (auxiliaryGenerators.horn_ι_mem h0 hn)
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Both actual endpoint corners in every dimension admit the prescribed diagonal. -/
theorem exists_endpointCorner_lift {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryGenerators.rlp p) (n : ℕ) (ε : Fin 2)
    {a : pushout (SSet.boundary.{u} n).ι
      ((productPrecylinder.{u}.app (SSet.boundary.{u} n : SSet)).endpoint ε) ⟶ X}
    {b : productPrecylinder.{u}.I.obj (Δ[n] : SSet) ⟶ Y}
    (sq : CommSq a (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε) p b) :
    ∃ l : productPrecylinder.{u}.I.obj (Δ[n] : SSet) ⟶ X,
      productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε ≫ l = a ∧ l ≫ p = b := by
  have h : HasLiftingProperty (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} n).ι ε) p :=
    hp _ (auxiliaryGenerators.endpointCorner_mem n ε)
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The zero-corner arrow isomorphism gives a diagonal at either original endpoint. -/
theorem exists_intervalEndpoint_lift {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryGenerators.rlp p) (ε : Fin 2)
    {a : (Δ[0] : SSet.{u}) ⟶ X} {b : SSet.joyalInterval.{u} ⟶ Y}
    (sq : CommSq a (endpoint.{u} ε) p b) :
    ∃ l : SSet.joyalInterval.{u} ⟶ X, endpoint.{u} ε ≫ l = a ∧ l ≫ p = b := by
  have h0 : HasLiftingProperty
      (productPrecylinder.{u}.endpointCorner (SSet.boundary.{u} 0).ι ε) p :=
    hp _ (auxiliaryGenerators.endpointCorner_mem 0 ε)
  have h : HasLiftingProperty (endpoint.{u} ε) p :=
    (HasLiftingProperty.iff_of_arrow_iso_left (endpointCornerZeroIso.{u} ε) p).mp h0
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGenerators
