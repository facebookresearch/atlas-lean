/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFactorization

/-!
# Public use of the chosen auxiliary factorization

The specified datum gives actual factor maps and intermediate maps along
arbitrary arrow squares. The native weak factorization-system interface
also supplies full prescribed diagonals.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory SSet.joyalInterval

universe u

namespace FiniteJoyalIntervalFactorizationTest

/-- The chosen countable datum gives actual factor maps with the full factor equation. -/
lemma exists_factorization {X Y : SSet.{u}} (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      i ≫ p = f ∧ auxiliaryAnodyneExtensions i ∧ auxiliaryNaiveFibrations p := by
  let d := auxiliaryFunctorialFactorizationData.factorizationData f
  exact ⟨d.Z, d.i, d.p, d.fac, d.hi, d.hp⟩

/-- Every arrow square induces an intermediate map retaining both naturality equations. -/
lemma exists_intermediate_map {X Y X' Y' : SSet.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (φ : Arrow.mk f ⟶ Arrow.mk g) :
    ∃ m : (auxiliaryFunctorialFactorizationData.factorizationData f).Z ⟶
        (auxiliaryFunctorialFactorizationData.factorizationData g).Z,
      (auxiliaryFunctorialFactorizationData.factorizationData f).i ≫ m =
        φ.left ≫ (auxiliaryFunctorialFactorizationData.factorizationData g).i ∧
      m ≫ (auxiliaryFunctorialFactorizationData.factorizationData g).p =
        (auxiliaryFunctorialFactorizationData.factorizationData f).p ≫ φ.right :=
  ⟨auxiliaryFunctorialFactorizationData.mapZ φ,
    auxiliaryFunctorialFactorizationData.i_mapZ φ,
    auxiliaryFunctorialFactorizationData.mapZ_p φ⟩

/-- The native weak factorization-system API supplies both prescribed lift equations. -/
lemma exists_lift {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : auxiliaryAnodyneExtensions i) (hp : auxiliaryNaiveFibrations p)
    {a : A ⟶ X} {b : B ⟶ Y} (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have h : HasLiftingProperty i p := MorphismProperty.hasLiftingProperty_of_wfs i p hi hp
  have : sq.HasLift := h.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end FiniteJoyalIntervalFactorizationTest
