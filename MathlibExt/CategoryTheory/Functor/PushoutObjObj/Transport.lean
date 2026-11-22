/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Transporting pushout-product data

Transports a chosen pushout-object pair along equality of the complete bifunctors. The resulting
corner arrow retains the original dependent equality.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uA vA uB vB uC vC
open CategoryTheory

namespace CategoryTheory.Functor.PushoutObjObj

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C]

/-- Whole actual bifunctor equality transports the same given pushout data and Arrow. -/
def transport {F G : A ⥤ B ⥤ C} (h : F = G)
    {M N : A} {X Y : B} {i : M ⟶ N} {j : X ⟶ Y}
    (sq : F.PushoutObjObj i j) : G.PushoutObjObj i j := by
  subst G
  exact sq

/-- The complete original pushout-product Arrow remains the same through whole functor equality. -/
theorem transport_arrow_heq {F G : A ⥤ B ⥤ C} (h : F = G)
    {M N : A} {X Y : B} {i : M ⟶ N} {j : X ⟶ Y}
    (sq : F.PushoutObjObj i j) : HEq (transport h sq).ι sq.ι := by
  subst G
  rfl

end CategoryTheory.Functor.PushoutObjObj
