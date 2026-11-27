/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uA vA uB vB uC vC
open CategoryTheory

namespace CategoryTheory.Functor.PushoutObjObj

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C]

/-- Transport the given pushout data along an equality of bifunctors. -/
def transport {F G : A ⥤ B ⥤ C} (h : F = G)
    {M N : A} {X Y : B} {i : M ⟶ N} {j : X ⟶ Y}
    (sq : F.PushoutObjObj i j) : G.PushoutObjObj i j := by
  subst G
  exact sq

/-- The transported corner morphism is heterogeneously equal to the original. -/
theorem transport_arrow_heq {F G : A ⥤ B ⥤ C} (h : F = G)
    {M N : A} {X Y : B} {i : M ⟶ N} {j : X ⟶ Y}
    (sq : F.PushoutObjObj i j) : HEq (transport h sq).ι sq.ι := by
  subst G
  rfl

end CategoryTheory.Functor.PushoutObjObj
