/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA vA uB vB uC vC
open CategoryTheory

namespace CategoryTheory.AdjunctionComparisonHEq

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C]

/-- Whole endpoint transport retains every map of the original actual natural isomorphism. -/
theorem eqToIso_symm_trans {F F' G : A ⥤ B} (hF : F = F') (r : F ≅ G) :
    HEq (eqToIso hF.symm ≪≫ r) r := by
  cases hF
  exact heq_of_eq (by ext X; simp)

/-- Actual transported adjunctions retain both complete original adjunction records. -/
theorem ofNatIsoRight {L L' : A ⥤ B} {R R' G : B ⥤ A}
    (hL : L = L') (hR : R = R') (adj : L ⊣ R) (adj' : L' ⊣ R')
    (ha : HEq adj adj') (r : R ≅ G) (r' : R' ≅ G) (hr : HEq r r') :
    HEq (adj.ofNatIsoRight r) (adj'.ofNatIsoRight r') := by
  cases hL
  cases hR
  cases ha
  cases hr
  rfl

/-- Original adjoint uniqueness retains every actual component after endpoint equality. -/
theorem leftAdjointUniq {L L' F : A ⥤ B} {R : B ⥤ A}
    (hL : L = L') (adj : F ⊣ R) (a : L ⊣ R) (a' : L' ⊣ R) (ha : HEq a a') :
    HEq (Adjunction.leftAdjointUniq adj a) (Adjunction.leftAdjointUniq adj a') := by
  cases hL
  cases ha
  rfl

/-- The actual complete whiskering retains all original natural isomorphism maps. -/
theorem whiskerRight {L L' F : A ⥤ B} (hL : L = L')
    (r : F ≅ L) (r' : F ≅ L') (hr : HEq r r') (U : B ⥤ C) :
    HEq (Functor.isoWhiskerRight r U) (Functor.isoWhiskerRight r' U) := by
  cases hL
  cases hr
  rfl

/-- Whole comparison composition retains both actual factors and every original endpoint. -/
theorem trans {F G G' H : A ⥤ B} (hG : G = G')
    (r : F ≅ G) (r' : F ≅ G') (hr : HEq r r')
    (s : G ≅ H) (s' : G' ≅ H) (hs : HEq s s') :
    r ≪≫ s = r' ≪≫ s' := by
  cases hG
  cases hr
  cases hs
  rfl

end CategoryTheory.AdjunctionComparisonHEq
